%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:54 EST 2020

% Result     : Theorem 10.12s
% Output     : CNFRefutation 10.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 266 expanded)
%              Number of leaves         :   45 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  226 ( 885 expanded)
%              Number of equality atoms :   41 ( 171 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(c_44,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_326,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_338,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_326])).

tff(c_269,plain,(
    ! [A_110,B_111,C_112] :
      ( k2_relset_1(A_110,B_111,C_112) = k2_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_282,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_269])).

tff(c_42,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_287,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_42])).

tff(c_342,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_287])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_490,plain,(
    ! [C_143,D_141,E_144,F_142,B_145,A_140] :
      ( k1_funct_1(k8_funct_2(B_145,C_143,A_140,D_141,E_144),F_142) = k1_funct_1(E_144,k1_funct_1(D_141,F_142))
      | k1_xboole_0 = B_145
      | ~ r1_tarski(k2_relset_1(B_145,C_143,D_141),k1_relset_1(C_143,A_140,E_144))
      | ~ m1_subset_1(F_142,B_145)
      | ~ m1_subset_1(E_144,k1_zfmisc_1(k2_zfmisc_1(C_143,A_140)))
      | ~ v1_funct_1(E_144)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(B_145,C_143)))
      | ~ v1_funct_2(D_141,B_145,C_143)
      | ~ v1_funct_1(D_141)
      | v1_xboole_0(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_498,plain,(
    ! [B_145,D_141,F_142] :
      ( k1_funct_1(k8_funct_2(B_145,'#skF_4','#skF_2',D_141,'#skF_6'),F_142) = k1_funct_1('#skF_6',k1_funct_1(D_141,F_142))
      | k1_xboole_0 = B_145
      | ~ r1_tarski(k2_relset_1(B_145,'#skF_4',D_141),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_142,B_145)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(B_145,'#skF_4')))
      | ~ v1_funct_2(D_141,B_145,'#skF_4')
      | ~ v1_funct_1(D_141)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_490])).

tff(c_506,plain,(
    ! [B_145,D_141,F_142] :
      ( k1_funct_1(k8_funct_2(B_145,'#skF_4','#skF_2',D_141,'#skF_6'),F_142) = k1_funct_1('#skF_6',k1_funct_1(D_141,F_142))
      | k1_xboole_0 = B_145
      | ~ r1_tarski(k2_relset_1(B_145,'#skF_4',D_141),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_142,B_145)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(B_145,'#skF_4')))
      | ~ v1_funct_2(D_141,B_145,'#skF_4')
      | ~ v1_funct_1(D_141)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_498])).

tff(c_10143,plain,(
    ! [B_1501,D_1502,F_1503] :
      ( k1_funct_1(k8_funct_2(B_1501,'#skF_4','#skF_2',D_1502,'#skF_6'),F_1503) = k1_funct_1('#skF_6',k1_funct_1(D_1502,F_1503))
      | k1_xboole_0 = B_1501
      | ~ r1_tarski(k2_relset_1(B_1501,'#skF_4',D_1502),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_1503,B_1501)
      | ~ m1_subset_1(D_1502,k1_zfmisc_1(k2_zfmisc_1(B_1501,'#skF_4')))
      | ~ v1_funct_2(D_1502,B_1501,'#skF_4')
      | ~ v1_funct_1(D_1502) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_506])).

tff(c_10148,plain,(
    ! [F_1503] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_1503) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_1503))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_1503,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_10143])).

tff(c_10150,plain,(
    ! [F_1503] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_1503) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_1503))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_1503,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_342,c_10148])).

tff(c_10151,plain,(
    ! [F_1503] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_1503) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_1503))
      | ~ m1_subset_1(F_1503,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_10150])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_217,plain,(
    ! [C_99,A_100,B_101] :
      ( r2_hidden(C_99,A_100)
      | ~ r2_hidden(C_99,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_524,plain,(
    ! [A_150,A_151,B_152] :
      ( r2_hidden(A_150,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_151))
      | v1_xboole_0(B_152)
      | ~ m1_subset_1(A_150,B_152) ) ),
    inference(resolution,[status(thm)],[c_12,c_217])).

tff(c_10165,plain,(
    ! [A_1506,B_1507,A_1508] :
      ( r2_hidden(A_1506,B_1507)
      | v1_xboole_0(A_1508)
      | ~ m1_subset_1(A_1506,A_1508)
      | ~ r1_tarski(A_1508,B_1507) ) ),
    inference(resolution,[status(thm)],[c_16,c_524])).

tff(c_10177,plain,(
    ! [B_1507] :
      ( r2_hidden('#skF_7',B_1507)
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski('#skF_3',B_1507) ) ),
    inference(resolution,[status(thm)],[c_44,c_10165])).

tff(c_10178,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_10177])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10198,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10178,c_6])).

tff(c_10202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_10198])).

tff(c_10204,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_10177])).

tff(c_122,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_134,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_122])).

tff(c_20,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_105,plain,(
    ! [B_83,A_84] :
      ( v1_relat_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_105])).

tff(c_118,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_111])).

tff(c_429,plain,(
    ! [D_133,C_134,A_135,B_136] :
      ( r2_hidden(k1_funct_1(D_133,C_134),k2_relset_1(A_135,B_136,D_133))
      | k1_xboole_0 = B_136
      | ~ r2_hidden(C_134,A_135)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_2(D_133,A_135,B_136)
      | ~ v1_funct_1(D_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_443,plain,(
    ! [C_134] :
      ( r2_hidden(k1_funct_1('#skF_5',C_134),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_134,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_429])).

tff(c_451,plain,(
    ! [C_134] :
      ( r2_hidden(k1_funct_1('#skF_5',C_134),k2_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_134,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_443])).

tff(c_461,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_451])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_75] :
      ( v1_xboole_0(A_75)
      | r2_hidden('#skF_1'(A_75),A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_71,plain,(
    ! [A_76] :
      ( ~ r1_tarski(A_76,'#skF_1'(A_76))
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_62,c_22])).

tff(c_76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_71])).

tff(c_470,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_76])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_470])).

tff(c_478,plain,(
    ! [C_139] :
      ( r2_hidden(k1_funct_1('#skF_5',C_139),k2_relat_1('#skF_5'))
      | ~ r2_hidden(C_139,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_451])).

tff(c_10,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10884,plain,(
    ! [C_1569,A_1570] :
      ( r2_hidden(k1_funct_1('#skF_5',C_1569),A_1570)
      | ~ m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1(A_1570))
      | ~ r2_hidden(C_1569,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_478,c_10])).

tff(c_10893,plain,(
    ! [C_1571,B_1572] :
      ( r2_hidden(k1_funct_1('#skF_5',C_1571),B_1572)
      | ~ r2_hidden(C_1571,'#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_1572) ) ),
    inference(resolution,[status(thm)],[c_16,c_10884])).

tff(c_32,plain,(
    ! [A_31,B_32,C_34] :
      ( k7_partfun1(A_31,B_32,C_34) = k1_funct_1(B_32,C_34)
      | ~ r2_hidden(C_34,k1_relat_1(B_32))
      | ~ v1_funct_1(B_32)
      | ~ v5_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12270,plain,(
    ! [A_1784,B_1785,C_1786] :
      ( k7_partfun1(A_1784,B_1785,k1_funct_1('#skF_5',C_1786)) = k1_funct_1(B_1785,k1_funct_1('#skF_5',C_1786))
      | ~ v1_funct_1(B_1785)
      | ~ v5_relat_1(B_1785,A_1784)
      | ~ v1_relat_1(B_1785)
      | ~ r2_hidden(C_1786,'#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1(B_1785)) ) ),
    inference(resolution,[status(thm)],[c_10893,c_32])).

tff(c_12274,plain,(
    ! [A_1784,C_1786] :
      ( k7_partfun1(A_1784,'#skF_6',k1_funct_1('#skF_5',C_1786)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_1786))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_1784)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_1786,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_342,c_12270])).

tff(c_12290,plain,(
    ! [A_1791,C_1792] :
      ( k7_partfun1(A_1791,'#skF_6',k1_funct_1('#skF_5',C_1792)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_1792))
      | ~ v5_relat_1('#skF_6',A_1791)
      | ~ r2_hidden(C_1792,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_48,c_12274])).

tff(c_38,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_12296,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12290,c_38])).

tff(c_12302,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_12296])).

tff(c_12304,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12302])).

tff(c_12310,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_12304])).

tff(c_12314,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12310])).

tff(c_12316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10204,c_12314])).

tff(c_12317,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_12302])).

tff(c_12361,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10151,c_12317])).

tff(c_12365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.12/3.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.12/4.00  
% 10.12/4.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.12/4.00  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 10.12/4.00  
% 10.12/4.00  %Foreground sorts:
% 10.12/4.00  
% 10.12/4.00  
% 10.12/4.00  %Background operators:
% 10.12/4.00  
% 10.12/4.00  
% 10.12/4.00  %Foreground operators:
% 10.12/4.00  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.12/4.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.12/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.12/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.12/4.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.12/4.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.12/4.00  tff('#skF_7', type, '#skF_7': $i).
% 10.12/4.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.12/4.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.12/4.00  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 10.12/4.00  tff('#skF_5', type, '#skF_5': $i).
% 10.12/4.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.12/4.00  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 10.12/4.00  tff('#skF_6', type, '#skF_6': $i).
% 10.12/4.00  tff('#skF_2', type, '#skF_2': $i).
% 10.12/4.00  tff('#skF_3', type, '#skF_3': $i).
% 10.12/4.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.12/4.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.12/4.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.12/4.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.12/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.12/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.12/4.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.12/4.00  tff('#skF_4', type, '#skF_4': $i).
% 10.12/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.12/4.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.12/4.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.12/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.12/4.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.12/4.00  
% 10.22/4.02  tff(f_154, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 10.22/4.02  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.22/4.02  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.22/4.02  tff(f_117, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 10.22/4.02  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.22/4.02  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.22/4.02  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 10.22/4.02  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.22/4.02  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.22/4.02  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.22/4.02  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.22/4.02  tff(f_129, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 10.22/4.02  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.22/4.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.22/4.02  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.22/4.02  tff(f_93, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 10.22/4.02  tff(c_44, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_326, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.22/4.02  tff(c_338, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_326])).
% 10.22/4.02  tff(c_269, plain, (![A_110, B_111, C_112]: (k2_relset_1(A_110, B_111, C_112)=k2_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.22/4.02  tff(c_282, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_269])).
% 10.22/4.02  tff(c_42, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_287, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_42])).
% 10.22/4.02  tff(c_342, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_287])).
% 10.22/4.02  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_490, plain, (![C_143, D_141, E_144, F_142, B_145, A_140]: (k1_funct_1(k8_funct_2(B_145, C_143, A_140, D_141, E_144), F_142)=k1_funct_1(E_144, k1_funct_1(D_141, F_142)) | k1_xboole_0=B_145 | ~r1_tarski(k2_relset_1(B_145, C_143, D_141), k1_relset_1(C_143, A_140, E_144)) | ~m1_subset_1(F_142, B_145) | ~m1_subset_1(E_144, k1_zfmisc_1(k2_zfmisc_1(C_143, A_140))) | ~v1_funct_1(E_144) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(B_145, C_143))) | ~v1_funct_2(D_141, B_145, C_143) | ~v1_funct_1(D_141) | v1_xboole_0(C_143))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.22/4.02  tff(c_498, plain, (![B_145, D_141, F_142]: (k1_funct_1(k8_funct_2(B_145, '#skF_4', '#skF_2', D_141, '#skF_6'), F_142)=k1_funct_1('#skF_6', k1_funct_1(D_141, F_142)) | k1_xboole_0=B_145 | ~r1_tarski(k2_relset_1(B_145, '#skF_4', D_141), k1_relat_1('#skF_6')) | ~m1_subset_1(F_142, B_145) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(B_145, '#skF_4'))) | ~v1_funct_2(D_141, B_145, '#skF_4') | ~v1_funct_1(D_141) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_338, c_490])).
% 10.22/4.02  tff(c_506, plain, (![B_145, D_141, F_142]: (k1_funct_1(k8_funct_2(B_145, '#skF_4', '#skF_2', D_141, '#skF_6'), F_142)=k1_funct_1('#skF_6', k1_funct_1(D_141, F_142)) | k1_xboole_0=B_145 | ~r1_tarski(k2_relset_1(B_145, '#skF_4', D_141), k1_relat_1('#skF_6')) | ~m1_subset_1(F_142, B_145) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(B_145, '#skF_4'))) | ~v1_funct_2(D_141, B_145, '#skF_4') | ~v1_funct_1(D_141) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_498])).
% 10.22/4.02  tff(c_10143, plain, (![B_1501, D_1502, F_1503]: (k1_funct_1(k8_funct_2(B_1501, '#skF_4', '#skF_2', D_1502, '#skF_6'), F_1503)=k1_funct_1('#skF_6', k1_funct_1(D_1502, F_1503)) | k1_xboole_0=B_1501 | ~r1_tarski(k2_relset_1(B_1501, '#skF_4', D_1502), k1_relat_1('#skF_6')) | ~m1_subset_1(F_1503, B_1501) | ~m1_subset_1(D_1502, k1_zfmisc_1(k2_zfmisc_1(B_1501, '#skF_4'))) | ~v1_funct_2(D_1502, B_1501, '#skF_4') | ~v1_funct_1(D_1502))), inference(negUnitSimplification, [status(thm)], [c_56, c_506])).
% 10.22/4.02  tff(c_10148, plain, (![F_1503]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_1503)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_1503)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1(F_1503, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_282, c_10143])).
% 10.22/4.02  tff(c_10150, plain, (![F_1503]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_1503)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_1503)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_1503, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_342, c_10148])).
% 10.22/4.02  tff(c_10151, plain, (![F_1503]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_1503)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_1503)) | ~m1_subset_1(F_1503, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_10150])).
% 10.22/4.02  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.22/4.02  tff(c_12, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.22/4.02  tff(c_217, plain, (![C_99, A_100, B_101]: (r2_hidden(C_99, A_100) | ~r2_hidden(C_99, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.22/4.02  tff(c_524, plain, (![A_150, A_151, B_152]: (r2_hidden(A_150, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(A_151)) | v1_xboole_0(B_152) | ~m1_subset_1(A_150, B_152))), inference(resolution, [status(thm)], [c_12, c_217])).
% 10.22/4.02  tff(c_10165, plain, (![A_1506, B_1507, A_1508]: (r2_hidden(A_1506, B_1507) | v1_xboole_0(A_1508) | ~m1_subset_1(A_1506, A_1508) | ~r1_tarski(A_1508, B_1507))), inference(resolution, [status(thm)], [c_16, c_524])).
% 10.22/4.02  tff(c_10177, plain, (![B_1507]: (r2_hidden('#skF_7', B_1507) | v1_xboole_0('#skF_3') | ~r1_tarski('#skF_3', B_1507))), inference(resolution, [status(thm)], [c_44, c_10165])).
% 10.22/4.02  tff(c_10178, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_10177])).
% 10.22/4.02  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.22/4.02  tff(c_10198, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10178, c_6])).
% 10.22/4.02  tff(c_10202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_10198])).
% 10.22/4.02  tff(c_10204, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_10177])).
% 10.22/4.02  tff(c_122, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.22/4.02  tff(c_134, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_122])).
% 10.22/4.02  tff(c_20, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.22/4.02  tff(c_105, plain, (![B_83, A_84]: (v1_relat_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.22/4.02  tff(c_111, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_105])).
% 10.22/4.02  tff(c_118, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_111])).
% 10.22/4.02  tff(c_429, plain, (![D_133, C_134, A_135, B_136]: (r2_hidden(k1_funct_1(D_133, C_134), k2_relset_1(A_135, B_136, D_133)) | k1_xboole_0=B_136 | ~r2_hidden(C_134, A_135) | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_2(D_133, A_135, B_136) | ~v1_funct_1(D_133))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.22/4.02  tff(c_443, plain, (![C_134]: (r2_hidden(k1_funct_1('#skF_5', C_134), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_134, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_282, c_429])).
% 10.22/4.02  tff(c_451, plain, (![C_134]: (r2_hidden(k1_funct_1('#skF_5', C_134), k2_relat_1('#skF_5')) | k1_xboole_0='#skF_4' | ~r2_hidden(C_134, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_443])).
% 10.22/4.02  tff(c_461, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_451])).
% 10.22/4.02  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.22/4.02  tff(c_62, plain, (![A_75]: (v1_xboole_0(A_75) | r2_hidden('#skF_1'(A_75), A_75))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.22/4.02  tff(c_22, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.22/4.02  tff(c_71, plain, (![A_76]: (~r1_tarski(A_76, '#skF_1'(A_76)) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_62, c_22])).
% 10.22/4.02  tff(c_76, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_71])).
% 10.22/4.02  tff(c_470, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_76])).
% 10.22/4.02  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_470])).
% 10.22/4.02  tff(c_478, plain, (![C_139]: (r2_hidden(k1_funct_1('#skF_5', C_139), k2_relat_1('#skF_5')) | ~r2_hidden(C_139, '#skF_3'))), inference(splitRight, [status(thm)], [c_451])).
% 10.22/4.02  tff(c_10, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.22/4.02  tff(c_10884, plain, (![C_1569, A_1570]: (r2_hidden(k1_funct_1('#skF_5', C_1569), A_1570) | ~m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1(A_1570)) | ~r2_hidden(C_1569, '#skF_3'))), inference(resolution, [status(thm)], [c_478, c_10])).
% 10.22/4.02  tff(c_10893, plain, (![C_1571, B_1572]: (r2_hidden(k1_funct_1('#skF_5', C_1571), B_1572) | ~r2_hidden(C_1571, '#skF_3') | ~r1_tarski(k2_relat_1('#skF_5'), B_1572))), inference(resolution, [status(thm)], [c_16, c_10884])).
% 10.22/4.02  tff(c_32, plain, (![A_31, B_32, C_34]: (k7_partfun1(A_31, B_32, C_34)=k1_funct_1(B_32, C_34) | ~r2_hidden(C_34, k1_relat_1(B_32)) | ~v1_funct_1(B_32) | ~v5_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.22/4.02  tff(c_12270, plain, (![A_1784, B_1785, C_1786]: (k7_partfun1(A_1784, B_1785, k1_funct_1('#skF_5', C_1786))=k1_funct_1(B_1785, k1_funct_1('#skF_5', C_1786)) | ~v1_funct_1(B_1785) | ~v5_relat_1(B_1785, A_1784) | ~v1_relat_1(B_1785) | ~r2_hidden(C_1786, '#skF_3') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1(B_1785)))), inference(resolution, [status(thm)], [c_10893, c_32])).
% 10.22/4.02  tff(c_12274, plain, (![A_1784, C_1786]: (k7_partfun1(A_1784, '#skF_6', k1_funct_1('#skF_5', C_1786))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_1786)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_1784) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_1786, '#skF_3'))), inference(resolution, [status(thm)], [c_342, c_12270])).
% 10.22/4.02  tff(c_12290, plain, (![A_1791, C_1792]: (k7_partfun1(A_1791, '#skF_6', k1_funct_1('#skF_5', C_1792))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_1792)) | ~v5_relat_1('#skF_6', A_1791) | ~r2_hidden(C_1792, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_48, c_12274])).
% 10.22/4.02  tff(c_38, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.22/4.02  tff(c_12296, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12290, c_38])).
% 10.22/4.02  tff(c_12302, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_12296])).
% 10.22/4.02  tff(c_12304, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_12302])).
% 10.22/4.02  tff(c_12310, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_12304])).
% 10.22/4.02  tff(c_12314, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12310])).
% 10.22/4.02  tff(c_12316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10204, c_12314])).
% 10.22/4.02  tff(c_12317, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_12302])).
% 10.22/4.02  tff(c_12361, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10151, c_12317])).
% 10.22/4.02  tff(c_12365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_12361])).
% 10.22/4.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.22/4.02  
% 10.22/4.02  Inference rules
% 10.22/4.02  ----------------------
% 10.22/4.02  #Ref     : 0
% 10.22/4.02  #Sup     : 2950
% 10.22/4.02  #Fact    : 0
% 10.22/4.02  #Define  : 0
% 10.22/4.02  #Split   : 183
% 10.22/4.02  #Chain   : 0
% 10.22/4.02  #Close   : 0
% 10.22/4.02  
% 10.22/4.02  Ordering : KBO
% 10.22/4.02  
% 10.22/4.02  Simplification rules
% 10.22/4.02  ----------------------
% 10.22/4.02  #Subsume      : 1355
% 10.22/4.02  #Demod        : 1325
% 10.22/4.02  #Tautology    : 353
% 10.22/4.02  #SimpNegUnit  : 202
% 10.22/4.02  #BackRed      : 96
% 10.22/4.02  
% 10.22/4.02  #Partial instantiations: 0
% 10.22/4.02  #Strategies tried      : 1
% 10.22/4.02  
% 10.22/4.02  Timing (in seconds)
% 10.22/4.02  ----------------------
% 10.26/4.02  Preprocessing        : 0.34
% 10.26/4.02  Parsing              : 0.18
% 10.26/4.02  CNF conversion       : 0.03
% 10.26/4.02  Main loop            : 2.90
% 10.26/4.02  Inferencing          : 0.79
% 10.26/4.02  Reduction            : 0.96
% 10.26/4.02  Demodulation         : 0.60
% 10.26/4.02  BG Simplification    : 0.07
% 10.26/4.02  Subsumption          : 0.88
% 10.26/4.02  Abstraction          : 0.09
% 10.26/4.02  MUC search           : 0.00
% 10.26/4.02  Cooper               : 0.00
% 10.26/4.02  Total                : 3.28
% 10.26/4.02  Index Insertion      : 0.00
% 10.26/4.02  Index Deletion       : 0.00
% 10.26/4.02  Index Matching       : 0.00
% 10.26/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
