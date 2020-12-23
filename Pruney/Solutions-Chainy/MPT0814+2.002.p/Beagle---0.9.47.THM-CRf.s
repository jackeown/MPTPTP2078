%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:51 EST 2020

% Result     : Theorem 20.50s
% Output     : CNFRefutation 20.54s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 105 expanded)
%              Number of leaves         :   39 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 205 expanded)
%              Number of equality atoms :    9 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_15 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden('#skF_1'(A_72,B_73),B_73)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_54,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_55,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,(
    v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_54,c_55])).

tff(c_107,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_111,plain,(
    v4_relat_1('#skF_15','#skF_13') ),
    inference(resolution,[status(thm)],[c_54,c_107])).

tff(c_52,plain,(
    r2_hidden('#skF_12','#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_68,plain,(
    ! [C_75,B_76,A_77] :
      ( r2_hidden(C_75,B_76)
      | ~ r2_hidden(C_75,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [B_76] :
      ( r2_hidden('#skF_12',B_76)
      | ~ r1_tarski('#skF_15',B_76) ) ),
    inference(resolution,[status(thm)],[c_52,c_68])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_291,plain,(
    ! [A_142,B_143,C_144] :
      ( k4_tarski('#skF_2'(A_142,B_143,C_144),'#skF_3'(A_142,B_143,C_144)) = A_142
      | ~ r2_hidden(A_142,k2_zfmisc_1(B_143,C_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [C_34,A_19,D_37] :
      ( r2_hidden(C_34,k1_relat_1(A_19))
      | ~ r2_hidden(k4_tarski(C_34,D_37),A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_415,plain,(
    ! [A_173,B_174,C_175,A_176] :
      ( r2_hidden('#skF_2'(A_173,B_174,C_175),k1_relat_1(A_176))
      | ~ r2_hidden(A_173,A_176)
      | ~ r2_hidden(A_173,k2_zfmisc_1(B_174,C_175)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_22])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8832,plain,(
    ! [B_628,C_625,A_627,B_629,A_626] :
      ( r2_hidden('#skF_2'(A_626,B_628,C_625),B_629)
      | ~ r1_tarski(k1_relat_1(A_627),B_629)
      | ~ r2_hidden(A_626,A_627)
      | ~ r2_hidden(A_626,k2_zfmisc_1(B_628,C_625)) ) ),
    inference(resolution,[status(thm)],[c_415,c_2])).

tff(c_37765,plain,(
    ! [C_1325,B_1326,A_1324,A_1328,B_1327] :
      ( r2_hidden('#skF_2'(A_1324,B_1327,C_1325),A_1328)
      | ~ r2_hidden(A_1324,B_1326)
      | ~ r2_hidden(A_1324,k2_zfmisc_1(B_1327,C_1325))
      | ~ v4_relat_1(B_1326,A_1328)
      | ~ v1_relat_1(B_1326) ) ),
    inference(resolution,[status(thm)],[c_14,c_8832])).

tff(c_38941,plain,(
    ! [B_1344,C_1345,A_1346,B_1347] :
      ( r2_hidden('#skF_2'('#skF_12',B_1344,C_1345),A_1346)
      | ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1344,C_1345))
      | ~ v4_relat_1(B_1347,A_1346)
      | ~ v1_relat_1(B_1347)
      | ~ r1_tarski('#skF_15',B_1347) ) ),
    inference(resolution,[status(thm)],[c_74,c_37765])).

tff(c_38995,plain,(
    ! [B_1344,C_1345] :
      ( r2_hidden('#skF_2'('#skF_12',B_1344,C_1345),'#skF_13')
      | ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1344,C_1345))
      | ~ v1_relat_1('#skF_15')
      | ~ r1_tarski('#skF_15','#skF_15') ) ),
    inference(resolution,[status(thm)],[c_111,c_38941])).

tff(c_39026,plain,(
    ! [B_1344,C_1345] :
      ( r2_hidden('#skF_2'('#skF_12',B_1344,C_1345),'#skF_13')
      | ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1344,C_1345)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_59,c_38995])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( k4_tarski('#skF_2'(A_6,B_7,C_8),'#skF_3'(A_6,B_7,C_8)) = A_6
      | ~ r2_hidden(A_6,k2_zfmisc_1(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [C_89,B_90,A_91] :
      ( v5_relat_1(C_89,B_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_101,plain,(
    v5_relat_1('#skF_15','#skF_14') ),
    inference(resolution,[status(thm)],[c_54,c_97])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [C_53,A_38,D_56] :
      ( r2_hidden(C_53,k2_relat_1(A_38))
      | ~ r2_hidden(k4_tarski(D_56,C_53),A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_360,plain,(
    ! [A_163,B_164,C_165,A_166] :
      ( r2_hidden('#skF_3'(A_163,B_164,C_165),k2_relat_1(A_166))
      | ~ r2_hidden(A_163,A_166)
      | ~ r2_hidden(A_163,k2_zfmisc_1(B_164,C_165)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_34])).

tff(c_10772,plain,(
    ! [A_715,B_712,C_711,A_713,B_714] :
      ( r2_hidden('#skF_3'(A_713,B_712,C_711),B_714)
      | ~ r1_tarski(k2_relat_1(A_715),B_714)
      | ~ r2_hidden(A_713,A_715)
      | ~ r2_hidden(A_713,k2_zfmisc_1(B_712,C_711)) ) ),
    inference(resolution,[status(thm)],[c_360,c_2])).

tff(c_42509,plain,(
    ! [A_1429,C_1431,B_1430,A_1428,B_1432] :
      ( r2_hidden('#skF_3'(A_1428,B_1432,C_1431),A_1429)
      | ~ r2_hidden(A_1428,B_1430)
      | ~ r2_hidden(A_1428,k2_zfmisc_1(B_1432,C_1431))
      | ~ v5_relat_1(B_1430,A_1429)
      | ~ v1_relat_1(B_1430) ) ),
    inference(resolution,[status(thm)],[c_18,c_10772])).

tff(c_42897,plain,(
    ! [B_1432,C_1431,A_1429] :
      ( r2_hidden('#skF_3'('#skF_12',B_1432,C_1431),A_1429)
      | ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1432,C_1431))
      | ~ v5_relat_1('#skF_15',A_1429)
      | ~ v1_relat_1('#skF_15') ) ),
    inference(resolution,[status(thm)],[c_52,c_42509])).

tff(c_43094,plain,(
    ! [B_1433,C_1434,A_1435] :
      ( r2_hidden('#skF_3'('#skF_12',B_1433,C_1434),A_1435)
      | ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1433,C_1434))
      | ~ v5_relat_1('#skF_15',A_1435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_42897])).

tff(c_50,plain,(
    ! [F_66,E_65] :
      ( ~ r2_hidden(F_66,'#skF_14')
      | ~ r2_hidden(E_65,'#skF_13')
      | k4_tarski(E_65,F_66) != '#skF_12' ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_43271,plain,(
    ! [E_65,B_1433,C_1434] :
      ( ~ r2_hidden(E_65,'#skF_13')
      | k4_tarski(E_65,'#skF_3'('#skF_12',B_1433,C_1434)) != '#skF_12'
      | ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1433,C_1434))
      | ~ v5_relat_1('#skF_15','#skF_14') ) ),
    inference(resolution,[status(thm)],[c_43094,c_50])).

tff(c_43337,plain,(
    ! [E_1436,B_1437,C_1438] :
      ( ~ r2_hidden(E_1436,'#skF_13')
      | k4_tarski(E_1436,'#skF_3'('#skF_12',B_1437,C_1438)) != '#skF_12'
      | ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1437,C_1438)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_43271])).

tff(c_43342,plain,(
    ! [B_1439,C_1440] :
      ( ~ r2_hidden('#skF_2'('#skF_12',B_1439,C_1440),'#skF_13')
      | ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1439,C_1440)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_43337])).

tff(c_43362,plain,(
    ! [B_1344,C_1345] : ~ r2_hidden('#skF_12',k2_zfmisc_1(B_1344,C_1345)) ),
    inference(resolution,[status(thm)],[c_39026,c_43342])).

tff(c_135,plain,(
    ! [C_105,A_106,B_107] :
      ( r2_hidden(C_105,A_106)
      | ~ r2_hidden(C_105,B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_145,plain,(
    ! [A_108] :
      ( r2_hidden('#skF_12',A_108)
      | ~ m1_subset_1('#skF_15',k1_zfmisc_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_52,c_135])).

tff(c_149,plain,(
    r2_hidden('#skF_12',k2_zfmisc_1('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_54,c_145])).

tff(c_43459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43362,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:53:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.50/12.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.54/12.43  
% 20.54/12.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.54/12.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_15 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4
% 20.54/12.43  
% 20.54/12.43  %Foreground sorts:
% 20.54/12.43  
% 20.54/12.43  
% 20.54/12.43  %Background operators:
% 20.54/12.43  
% 20.54/12.43  
% 20.54/12.43  %Foreground operators:
% 20.54/12.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 20.54/12.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.54/12.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.54/12.43  tff('#skF_15', type, '#skF_15': $i).
% 20.54/12.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 20.54/12.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.54/12.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.54/12.43  tff('#skF_14', type, '#skF_14': $i).
% 20.54/12.43  tff('#skF_13', type, '#skF_13': $i).
% 20.54/12.43  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 20.54/12.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.54/12.43  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 20.54/12.43  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 20.54/12.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 20.54/12.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.54/12.43  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 20.54/12.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.54/12.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.54/12.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.54/12.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 20.54/12.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.54/12.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 20.54/12.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.54/12.43  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 20.54/12.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 20.54/12.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.54/12.43  tff('#skF_12', type, '#skF_12': $i).
% 20.54/12.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.54/12.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.54/12.43  
% 20.54/12.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.54/12.44  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 20.54/12.44  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 20.54/12.44  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 20.54/12.44  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 20.54/12.44  tff(f_39, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 20.54/12.44  tff(f_66, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 20.54/12.44  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 20.54/12.44  tff(f_74, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 20.54/12.44  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 20.54/12.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.54/12.44  tff(c_61, plain, (![A_72, B_73]: (~r2_hidden('#skF_1'(A_72, B_73), B_73) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.54/12.44  tff(c_66, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_61])).
% 20.54/12.44  tff(c_54, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_14')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 20.54/12.44  tff(c_55, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 20.54/12.44  tff(c_59, plain, (v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_54, c_55])).
% 20.54/12.44  tff(c_107, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.54/12.44  tff(c_111, plain, (v4_relat_1('#skF_15', '#skF_13')), inference(resolution, [status(thm)], [c_54, c_107])).
% 20.54/12.44  tff(c_52, plain, (r2_hidden('#skF_12', '#skF_15')), inference(cnfTransformation, [status(thm)], [f_98])).
% 20.54/12.44  tff(c_68, plain, (![C_75, B_76, A_77]: (r2_hidden(C_75, B_76) | ~r2_hidden(C_75, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.54/12.44  tff(c_74, plain, (![B_76]: (r2_hidden('#skF_12', B_76) | ~r1_tarski('#skF_15', B_76))), inference(resolution, [status(thm)], [c_52, c_68])).
% 20.54/12.44  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.54/12.44  tff(c_291, plain, (![A_142, B_143, C_144]: (k4_tarski('#skF_2'(A_142, B_143, C_144), '#skF_3'(A_142, B_143, C_144))=A_142 | ~r2_hidden(A_142, k2_zfmisc_1(B_143, C_144)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.54/12.44  tff(c_22, plain, (![C_34, A_19, D_37]: (r2_hidden(C_34, k1_relat_1(A_19)) | ~r2_hidden(k4_tarski(C_34, D_37), A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.54/12.44  tff(c_415, plain, (![A_173, B_174, C_175, A_176]: (r2_hidden('#skF_2'(A_173, B_174, C_175), k1_relat_1(A_176)) | ~r2_hidden(A_173, A_176) | ~r2_hidden(A_173, k2_zfmisc_1(B_174, C_175)))), inference(superposition, [status(thm), theory('equality')], [c_291, c_22])).
% 20.54/12.44  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.54/12.44  tff(c_8832, plain, (![B_628, C_625, A_627, B_629, A_626]: (r2_hidden('#skF_2'(A_626, B_628, C_625), B_629) | ~r1_tarski(k1_relat_1(A_627), B_629) | ~r2_hidden(A_626, A_627) | ~r2_hidden(A_626, k2_zfmisc_1(B_628, C_625)))), inference(resolution, [status(thm)], [c_415, c_2])).
% 20.54/12.44  tff(c_37765, plain, (![C_1325, B_1326, A_1324, A_1328, B_1327]: (r2_hidden('#skF_2'(A_1324, B_1327, C_1325), A_1328) | ~r2_hidden(A_1324, B_1326) | ~r2_hidden(A_1324, k2_zfmisc_1(B_1327, C_1325)) | ~v4_relat_1(B_1326, A_1328) | ~v1_relat_1(B_1326))), inference(resolution, [status(thm)], [c_14, c_8832])).
% 20.54/12.44  tff(c_38941, plain, (![B_1344, C_1345, A_1346, B_1347]: (r2_hidden('#skF_2'('#skF_12', B_1344, C_1345), A_1346) | ~r2_hidden('#skF_12', k2_zfmisc_1(B_1344, C_1345)) | ~v4_relat_1(B_1347, A_1346) | ~v1_relat_1(B_1347) | ~r1_tarski('#skF_15', B_1347))), inference(resolution, [status(thm)], [c_74, c_37765])).
% 20.54/12.44  tff(c_38995, plain, (![B_1344, C_1345]: (r2_hidden('#skF_2'('#skF_12', B_1344, C_1345), '#skF_13') | ~r2_hidden('#skF_12', k2_zfmisc_1(B_1344, C_1345)) | ~v1_relat_1('#skF_15') | ~r1_tarski('#skF_15', '#skF_15'))), inference(resolution, [status(thm)], [c_111, c_38941])).
% 20.54/12.44  tff(c_39026, plain, (![B_1344, C_1345]: (r2_hidden('#skF_2'('#skF_12', B_1344, C_1345), '#skF_13') | ~r2_hidden('#skF_12', k2_zfmisc_1(B_1344, C_1345)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_59, c_38995])).
% 20.54/12.44  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_tarski('#skF_2'(A_6, B_7, C_8), '#skF_3'(A_6, B_7, C_8))=A_6 | ~r2_hidden(A_6, k2_zfmisc_1(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.54/12.44  tff(c_97, plain, (![C_89, B_90, A_91]: (v5_relat_1(C_89, B_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.54/12.44  tff(c_101, plain, (v5_relat_1('#skF_15', '#skF_14')), inference(resolution, [status(thm)], [c_54, c_97])).
% 20.54/12.44  tff(c_18, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.54/12.44  tff(c_34, plain, (![C_53, A_38, D_56]: (r2_hidden(C_53, k2_relat_1(A_38)) | ~r2_hidden(k4_tarski(D_56, C_53), A_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.54/12.44  tff(c_360, plain, (![A_163, B_164, C_165, A_166]: (r2_hidden('#skF_3'(A_163, B_164, C_165), k2_relat_1(A_166)) | ~r2_hidden(A_163, A_166) | ~r2_hidden(A_163, k2_zfmisc_1(B_164, C_165)))), inference(superposition, [status(thm), theory('equality')], [c_291, c_34])).
% 20.54/12.44  tff(c_10772, plain, (![A_715, B_712, C_711, A_713, B_714]: (r2_hidden('#skF_3'(A_713, B_712, C_711), B_714) | ~r1_tarski(k2_relat_1(A_715), B_714) | ~r2_hidden(A_713, A_715) | ~r2_hidden(A_713, k2_zfmisc_1(B_712, C_711)))), inference(resolution, [status(thm)], [c_360, c_2])).
% 20.54/12.44  tff(c_42509, plain, (![A_1429, C_1431, B_1430, A_1428, B_1432]: (r2_hidden('#skF_3'(A_1428, B_1432, C_1431), A_1429) | ~r2_hidden(A_1428, B_1430) | ~r2_hidden(A_1428, k2_zfmisc_1(B_1432, C_1431)) | ~v5_relat_1(B_1430, A_1429) | ~v1_relat_1(B_1430))), inference(resolution, [status(thm)], [c_18, c_10772])).
% 20.54/12.44  tff(c_42897, plain, (![B_1432, C_1431, A_1429]: (r2_hidden('#skF_3'('#skF_12', B_1432, C_1431), A_1429) | ~r2_hidden('#skF_12', k2_zfmisc_1(B_1432, C_1431)) | ~v5_relat_1('#skF_15', A_1429) | ~v1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_52, c_42509])).
% 20.54/12.44  tff(c_43094, plain, (![B_1433, C_1434, A_1435]: (r2_hidden('#skF_3'('#skF_12', B_1433, C_1434), A_1435) | ~r2_hidden('#skF_12', k2_zfmisc_1(B_1433, C_1434)) | ~v5_relat_1('#skF_15', A_1435))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_42897])).
% 20.54/12.44  tff(c_50, plain, (![F_66, E_65]: (~r2_hidden(F_66, '#skF_14') | ~r2_hidden(E_65, '#skF_13') | k4_tarski(E_65, F_66)!='#skF_12')), inference(cnfTransformation, [status(thm)], [f_98])).
% 20.54/12.44  tff(c_43271, plain, (![E_65, B_1433, C_1434]: (~r2_hidden(E_65, '#skF_13') | k4_tarski(E_65, '#skF_3'('#skF_12', B_1433, C_1434))!='#skF_12' | ~r2_hidden('#skF_12', k2_zfmisc_1(B_1433, C_1434)) | ~v5_relat_1('#skF_15', '#skF_14'))), inference(resolution, [status(thm)], [c_43094, c_50])).
% 20.54/12.44  tff(c_43337, plain, (![E_1436, B_1437, C_1438]: (~r2_hidden(E_1436, '#skF_13') | k4_tarski(E_1436, '#skF_3'('#skF_12', B_1437, C_1438))!='#skF_12' | ~r2_hidden('#skF_12', k2_zfmisc_1(B_1437, C_1438)))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_43271])).
% 20.54/12.44  tff(c_43342, plain, (![B_1439, C_1440]: (~r2_hidden('#skF_2'('#skF_12', B_1439, C_1440), '#skF_13') | ~r2_hidden('#skF_12', k2_zfmisc_1(B_1439, C_1440)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_43337])).
% 20.54/12.44  tff(c_43362, plain, (![B_1344, C_1345]: (~r2_hidden('#skF_12', k2_zfmisc_1(B_1344, C_1345)))), inference(resolution, [status(thm)], [c_39026, c_43342])).
% 20.54/12.44  tff(c_135, plain, (![C_105, A_106, B_107]: (r2_hidden(C_105, A_106) | ~r2_hidden(C_105, B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 20.54/12.44  tff(c_145, plain, (![A_108]: (r2_hidden('#skF_12', A_108) | ~m1_subset_1('#skF_15', k1_zfmisc_1(A_108)))), inference(resolution, [status(thm)], [c_52, c_135])).
% 20.54/12.44  tff(c_149, plain, (r2_hidden('#skF_12', k2_zfmisc_1('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_54, c_145])).
% 20.54/12.44  tff(c_43459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43362, c_149])).
% 20.54/12.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.54/12.44  
% 20.54/12.44  Inference rules
% 20.54/12.44  ----------------------
% 20.54/12.44  #Ref     : 0
% 20.54/12.44  #Sup     : 11399
% 20.54/12.44  #Fact    : 0
% 20.54/12.44  #Define  : 0
% 20.54/12.44  #Split   : 93
% 20.54/12.44  #Chain   : 0
% 20.54/12.44  #Close   : 0
% 20.54/12.44  
% 20.54/12.44  Ordering : KBO
% 20.54/12.44  
% 20.54/12.44  Simplification rules
% 20.54/12.44  ----------------------
% 20.54/12.45  #Subsume      : 1384
% 20.54/12.45  #Demod        : 79
% 20.54/12.45  #Tautology    : 185
% 20.54/12.45  #SimpNegUnit  : 1
% 20.54/12.45  #BackRed      : 1
% 20.54/12.45  
% 20.54/12.45  #Partial instantiations: 0
% 20.54/12.45  #Strategies tried      : 1
% 20.54/12.45  
% 20.54/12.45  Timing (in seconds)
% 20.54/12.45  ----------------------
% 20.54/12.45  Preprocessing        : 0.33
% 20.54/12.45  Parsing              : 0.18
% 20.54/12.45  CNF conversion       : 0.03
% 20.54/12.45  Main loop            : 11.30
% 20.54/12.45  Inferencing          : 1.63
% 20.54/12.45  Reduction            : 1.97
% 20.54/12.45  Demodulation         : 1.13
% 20.54/12.45  BG Simplification    : 0.19
% 20.54/12.45  Subsumption          : 6.84
% 20.54/12.45  Abstraction          : 0.29
% 20.54/12.45  MUC search           : 0.00
% 20.54/12.45  Cooper               : 0.00
% 20.54/12.45  Total                : 11.66
% 20.54/12.45  Index Insertion      : 0.00
% 20.54/12.45  Index Deletion       : 0.00
% 20.54/12.45  Index Matching       : 0.00
% 20.54/12.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
