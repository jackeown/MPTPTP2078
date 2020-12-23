%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:27 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 170 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  162 ( 384 expanded)
%              Number of equality atoms :    1 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_949,plain,(
    ! [D_147,B_148,C_149,A_150] :
      ( m1_subset_1(D_147,k1_zfmisc_1(k2_zfmisc_1(B_148,C_149)))
      | ~ r1_tarski(k1_relat_1(D_147),B_148)
      | ~ m1_subset_1(D_147,k1_zfmisc_1(k2_zfmisc_1(A_150,C_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1445,plain,(
    ! [A_199,B_200,C_201,A_202] :
      ( m1_subset_1(A_199,k1_zfmisc_1(k2_zfmisc_1(B_200,C_201)))
      | ~ r1_tarski(k1_relat_1(A_199),B_200)
      | ~ r1_tarski(A_199,k2_zfmisc_1(A_202,C_201)) ) ),
    inference(resolution,[status(thm)],[c_12,c_949])).

tff(c_1486,plain,(
    ! [B_203] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_203,'#skF_5')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_203) ) ),
    inference(resolution,[status(thm)],[c_40,c_1445])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1500,plain,(
    ! [B_204] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(B_204,'#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_204) ) ),
    inference(resolution,[status(thm)],[c_1486,c_10])).

tff(c_1534,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_1500])).

tff(c_36,plain,(
    ! [A_24,B_25,C_26] :
      ( v1_finset_1('#skF_1'(A_24,B_25,C_26))
      | ~ r1_tarski(A_24,k2_zfmisc_1(B_25,C_26))
      | ~ v1_finset_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1562,plain,
    ( v1_finset_1('#skF_1'('#skF_3',k1_relat_1('#skF_3'),'#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1534,c_36])).

tff(c_1608,plain,(
    v1_finset_1('#skF_1'('#skF_3',k1_relat_1('#skF_3'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1562])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1614,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_5'))
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1534,c_8])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_tarski(A_24,k2_zfmisc_1('#skF_1'(A_24,B_25,C_26),'#skF_2'(A_24,B_25,C_26)))
      | ~ r1_tarski(A_24,k2_zfmisc_1(B_25,C_26))
      | ~ v1_finset_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_13,B_14)),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    ! [A_38,B_39] :
      ( v1_finset_1(A_38)
      | ~ v1_finset_1(B_39)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,(
    ! [A_13,B_14] :
      ( v1_finset_1(k1_relat_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_finset_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_88,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(A_49)
      | ~ v1_relat_1(B_50)
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_12,c_88])).

tff(c_99,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_312,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k1_relat_1(A_94),k1_relat_1(B_95))
      | ~ r1_tarski(A_94,B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_108,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(B_53,C_52)
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [A_51,A_13,B_14] :
      ( r1_tarski(A_51,A_13)
      | ~ r1_tarski(A_51,k1_relat_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(resolution,[status(thm)],[c_18,c_108])).

tff(c_322,plain,(
    ! [A_94,A_13,B_14] :
      ( r1_tarski(k1_relat_1(A_94),A_13)
      | ~ r1_tarski(A_94,k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_312,c_115])).

tff(c_344,plain,(
    ! [A_96,A_97,B_98] :
      ( r1_tarski(k1_relat_1(A_96),A_97)
      | ~ r1_tarski(A_96,k2_zfmisc_1(A_97,B_98))
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_322])).

tff(c_356,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_344])).

tff(c_366,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_356])).

tff(c_38,plain,(
    ! [D_30] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(D_30,'#skF_5'))
      | ~ r1_tarski(D_30,'#skF_4')
      | ~ v1_finset_1(D_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1577,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_4')
    | ~ v1_finset_1(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1534,c_38])).

tff(c_1621,plain,(
    ~ v1_finset_1(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_1577])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k1_relat_1(A_15),k1_relat_1(B_17))
      | ~ r1_tarski(A_15,B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1515,plain,(
    ! [B_17] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1(B_17),'#skF_5'))
      | ~ r1_tarski('#skF_3',B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_1500])).

tff(c_1774,plain,(
    ! [B_210] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1(B_210),'#skF_5'))
      | ~ r1_tarski('#skF_3',B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1515])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( v1_finset_1(A_22)
      | ~ v1_finset_1(B_23)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_860,plain,(
    ! [A_140,B_141] :
      ( v1_finset_1(k1_relat_1(A_140))
      | ~ v1_finset_1(k1_relat_1(B_141))
      | ~ r1_tarski(A_140,B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_312,c_26])).

tff(c_864,plain,(
    ! [A_140,A_13,B_14] :
      ( v1_finset_1(k1_relat_1(A_140))
      | ~ r1_tarski(A_140,k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(A_140)
      | ~ v1_finset_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_58,c_860])).

tff(c_870,plain,(
    ! [A_140,A_13,B_14] :
      ( v1_finset_1(k1_relat_1(A_140))
      | ~ r1_tarski(A_140,k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(A_140)
      | ~ v1_finset_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_864])).

tff(c_1798,plain,(
    ! [B_210] :
      ( v1_finset_1(k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_finset_1(k1_relat_1(B_210))
      | ~ r1_tarski('#skF_3',B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(resolution,[status(thm)],[c_1774,c_870])).

tff(c_1850,plain,(
    ! [B_210] :
      ( v1_finset_1(k1_relat_1('#skF_3'))
      | ~ v1_finset_1(k1_relat_1(B_210))
      | ~ r1_tarski('#skF_3',B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1798])).

tff(c_1903,plain,(
    ! [B_215] :
      ( ~ v1_finset_1(k1_relat_1(B_215))
      | ~ r1_tarski('#skF_3',B_215)
      | ~ v1_relat_1(B_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1621,c_1850])).

tff(c_1912,plain,(
    ! [A_13,B_14] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(A_13,B_14))
      | ~ v1_relat_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_finset_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_58,c_1903])).

tff(c_1922,plain,(
    ! [A_216,B_217] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(A_216,B_217))
      | ~ v1_finset_1(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1912])).

tff(c_1936,plain,(
    ! [B_25,C_26] :
      ( ~ v1_finset_1('#skF_1'('#skF_3',B_25,C_26))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_25,C_26))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_1922])).

tff(c_2248,plain,(
    ! [B_239,C_240] :
      ( ~ v1_finset_1('#skF_1'('#skF_3',B_239,C_240))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_239,C_240)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1936])).

tff(c_2255,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_3',k1_relat_1('#skF_3'),'#skF_5'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1614,c_2248])).

tff(c_2274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1608,c_2255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:03:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.81  
% 4.62/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.82  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.62/1.82  
% 4.62/1.82  %Foreground sorts:
% 4.62/1.82  
% 4.62/1.82  
% 4.62/1.82  %Background operators:
% 4.62/1.82  
% 4.62/1.82  
% 4.62/1.82  %Foreground operators:
% 4.62/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.62/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.62/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.62/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.62/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.82  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 4.62/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.62/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.82  
% 4.94/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.94/1.84  tff(f_106, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 4.94/1.84  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.94/1.84  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 4.94/1.84  tff(f_92, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 4.94/1.84  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.94/1.84  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.94/1.84  tff(f_52, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 4.94/1.84  tff(f_75, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 4.94/1.84  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.94/1.84  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 4.94/1.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.94/1.84  tff(c_42, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.94/1.84  tff(c_40, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.94/1.84  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.94/1.84  tff(c_949, plain, (![D_147, B_148, C_149, A_150]: (m1_subset_1(D_147, k1_zfmisc_1(k2_zfmisc_1(B_148, C_149))) | ~r1_tarski(k1_relat_1(D_147), B_148) | ~m1_subset_1(D_147, k1_zfmisc_1(k2_zfmisc_1(A_150, C_149))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.94/1.84  tff(c_1445, plain, (![A_199, B_200, C_201, A_202]: (m1_subset_1(A_199, k1_zfmisc_1(k2_zfmisc_1(B_200, C_201))) | ~r1_tarski(k1_relat_1(A_199), B_200) | ~r1_tarski(A_199, k2_zfmisc_1(A_202, C_201)))), inference(resolution, [status(thm)], [c_12, c_949])).
% 4.94/1.84  tff(c_1486, plain, (![B_203]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_203, '#skF_5'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_203))), inference(resolution, [status(thm)], [c_40, c_1445])).
% 4.94/1.84  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.94/1.84  tff(c_1500, plain, (![B_204]: (r1_tarski('#skF_3', k2_zfmisc_1(B_204, '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_3'), B_204))), inference(resolution, [status(thm)], [c_1486, c_10])).
% 4.94/1.84  tff(c_1534, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_1500])).
% 4.94/1.84  tff(c_36, plain, (![A_24, B_25, C_26]: (v1_finset_1('#skF_1'(A_24, B_25, C_26)) | ~r1_tarski(A_24, k2_zfmisc_1(B_25, C_26)) | ~v1_finset_1(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.94/1.84  tff(c_1562, plain, (v1_finset_1('#skF_1'('#skF_3', k1_relat_1('#skF_3'), '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_1534, c_36])).
% 4.94/1.84  tff(c_1608, plain, (v1_finset_1('#skF_1'('#skF_3', k1_relat_1('#skF_3'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1562])).
% 4.94/1.84  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.94/1.84  tff(c_1614, plain, (![A_3]: (r1_tarski(A_3, k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_5')) | ~r1_tarski(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_1534, c_8])).
% 4.94/1.84  tff(c_28, plain, (![A_24, B_25, C_26]: (r1_tarski(A_24, k2_zfmisc_1('#skF_1'(A_24, B_25, C_26), '#skF_2'(A_24, B_25, C_26))) | ~r1_tarski(A_24, k2_zfmisc_1(B_25, C_26)) | ~v1_finset_1(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.94/1.84  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.94/1.84  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_13, B_14)), A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.94/1.84  tff(c_48, plain, (![A_38, B_39]: (v1_finset_1(A_38) | ~v1_finset_1(B_39) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.94/1.84  tff(c_58, plain, (![A_13, B_14]: (v1_finset_1(k1_relat_1(k2_zfmisc_1(A_13, B_14))) | ~v1_finset_1(A_13))), inference(resolution, [status(thm)], [c_18, c_48])).
% 4.94/1.84  tff(c_88, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.94/1.84  tff(c_93, plain, (![A_49, B_50]: (v1_relat_1(A_49) | ~v1_relat_1(B_50) | ~r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_12, c_88])).
% 4.94/1.84  tff(c_99, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_93])).
% 4.94/1.84  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_99])).
% 4.94/1.84  tff(c_312, plain, (![A_94, B_95]: (r1_tarski(k1_relat_1(A_94), k1_relat_1(B_95)) | ~r1_tarski(A_94, B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.94/1.84  tff(c_108, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(B_53, C_52) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.94/1.84  tff(c_115, plain, (![A_51, A_13, B_14]: (r1_tarski(A_51, A_13) | ~r1_tarski(A_51, k1_relat_1(k2_zfmisc_1(A_13, B_14))))), inference(resolution, [status(thm)], [c_18, c_108])).
% 4.94/1.84  tff(c_322, plain, (![A_94, A_13, B_14]: (r1_tarski(k1_relat_1(A_94), A_13) | ~r1_tarski(A_94, k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_312, c_115])).
% 4.94/1.84  tff(c_344, plain, (![A_96, A_97, B_98]: (r1_tarski(k1_relat_1(A_96), A_97) | ~r1_tarski(A_96, k2_zfmisc_1(A_97, B_98)) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_322])).
% 4.94/1.84  tff(c_356, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_344])).
% 4.94/1.84  tff(c_366, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_356])).
% 4.94/1.84  tff(c_38, plain, (![D_30]: (~r1_tarski('#skF_3', k2_zfmisc_1(D_30, '#skF_5')) | ~r1_tarski(D_30, '#skF_4') | ~v1_finset_1(D_30))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.94/1.84  tff(c_1577, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_4') | ~v1_finset_1(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1534, c_38])).
% 4.94/1.84  tff(c_1621, plain, (~v1_finset_1(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_1577])).
% 4.94/1.84  tff(c_22, plain, (![A_15, B_17]: (r1_tarski(k1_relat_1(A_15), k1_relat_1(B_17)) | ~r1_tarski(A_15, B_17) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.94/1.84  tff(c_1515, plain, (![B_17]: (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1(B_17), '#skF_5')) | ~r1_tarski('#skF_3', B_17) | ~v1_relat_1(B_17) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1500])).
% 4.94/1.84  tff(c_1774, plain, (![B_210]: (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1(B_210), '#skF_5')) | ~r1_tarski('#skF_3', B_210) | ~v1_relat_1(B_210))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1515])).
% 4.94/1.84  tff(c_26, plain, (![A_22, B_23]: (v1_finset_1(A_22) | ~v1_finset_1(B_23) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.94/1.84  tff(c_860, plain, (![A_140, B_141]: (v1_finset_1(k1_relat_1(A_140)) | ~v1_finset_1(k1_relat_1(B_141)) | ~r1_tarski(A_140, B_141) | ~v1_relat_1(B_141) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_312, c_26])).
% 4.94/1.84  tff(c_864, plain, (![A_140, A_13, B_14]: (v1_finset_1(k1_relat_1(A_140)) | ~r1_tarski(A_140, k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(A_140) | ~v1_finset_1(A_13))), inference(resolution, [status(thm)], [c_58, c_860])).
% 4.94/1.84  tff(c_870, plain, (![A_140, A_13, B_14]: (v1_finset_1(k1_relat_1(A_140)) | ~r1_tarski(A_140, k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(A_140) | ~v1_finset_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_864])).
% 4.94/1.84  tff(c_1798, plain, (![B_210]: (v1_finset_1(k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_finset_1(k1_relat_1(B_210)) | ~r1_tarski('#skF_3', B_210) | ~v1_relat_1(B_210))), inference(resolution, [status(thm)], [c_1774, c_870])).
% 4.94/1.84  tff(c_1850, plain, (![B_210]: (v1_finset_1(k1_relat_1('#skF_3')) | ~v1_finset_1(k1_relat_1(B_210)) | ~r1_tarski('#skF_3', B_210) | ~v1_relat_1(B_210))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1798])).
% 4.94/1.84  tff(c_1903, plain, (![B_215]: (~v1_finset_1(k1_relat_1(B_215)) | ~r1_tarski('#skF_3', B_215) | ~v1_relat_1(B_215))), inference(negUnitSimplification, [status(thm)], [c_1621, c_1850])).
% 4.94/1.84  tff(c_1912, plain, (![A_13, B_14]: (~r1_tarski('#skF_3', k2_zfmisc_1(A_13, B_14)) | ~v1_relat_1(k2_zfmisc_1(A_13, B_14)) | ~v1_finset_1(A_13))), inference(resolution, [status(thm)], [c_58, c_1903])).
% 4.94/1.84  tff(c_1922, plain, (![A_216, B_217]: (~r1_tarski('#skF_3', k2_zfmisc_1(A_216, B_217)) | ~v1_finset_1(A_216))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1912])).
% 4.94/1.84  tff(c_1936, plain, (![B_25, C_26]: (~v1_finset_1('#skF_1'('#skF_3', B_25, C_26)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_25, C_26)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_1922])).
% 4.94/1.84  tff(c_2248, plain, (![B_239, C_240]: (~v1_finset_1('#skF_1'('#skF_3', B_239, C_240)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_239, C_240)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1936])).
% 4.94/1.84  tff(c_2255, plain, (~v1_finset_1('#skF_1'('#skF_3', k1_relat_1('#skF_3'), '#skF_5')) | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1614, c_2248])).
% 4.94/1.84  tff(c_2274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1608, c_2255])).
% 4.94/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.94/1.84  
% 4.94/1.84  Inference rules
% 4.94/1.84  ----------------------
% 4.94/1.84  #Ref     : 0
% 4.94/1.84  #Sup     : 456
% 4.94/1.84  #Fact    : 0
% 4.94/1.84  #Define  : 0
% 4.94/1.84  #Split   : 9
% 4.94/1.84  #Chain   : 0
% 4.94/1.84  #Close   : 0
% 4.94/1.84  
% 4.94/1.84  Ordering : KBO
% 4.94/1.84  
% 4.94/1.84  Simplification rules
% 4.94/1.84  ----------------------
% 4.94/1.84  #Subsume      : 106
% 4.94/1.84  #Demod        : 160
% 4.94/1.84  #Tautology    : 49
% 4.94/1.84  #SimpNegUnit  : 6
% 4.94/1.84  #BackRed      : 0
% 4.94/1.84  
% 4.94/1.84  #Partial instantiations: 0
% 4.94/1.84  #Strategies tried      : 1
% 4.94/1.84  
% 4.94/1.84  Timing (in seconds)
% 4.94/1.84  ----------------------
% 4.94/1.84  Preprocessing        : 0.30
% 4.94/1.84  Parsing              : 0.17
% 4.94/1.84  CNF conversion       : 0.02
% 4.94/1.84  Main loop            : 0.76
% 4.94/1.84  Inferencing          : 0.26
% 4.94/1.84  Reduction            : 0.23
% 4.94/1.84  Demodulation         : 0.16
% 4.94/1.84  BG Simplification    : 0.03
% 4.94/1.84  Subsumption          : 0.18
% 4.94/1.84  Abstraction          : 0.03
% 4.94/1.84  MUC search           : 0.00
% 4.94/1.84  Cooper               : 0.00
% 4.94/1.84  Total                : 1.12
% 4.94/1.84  Index Insertion      : 0.00
% 4.94/1.84  Index Deletion       : 0.00
% 4.94/1.84  Index Matching       : 0.00
% 4.94/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
