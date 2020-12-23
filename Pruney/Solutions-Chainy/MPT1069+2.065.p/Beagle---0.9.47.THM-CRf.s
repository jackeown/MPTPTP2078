%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:54 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 289 expanded)
%              Number of leaves         :   43 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          :  248 (1056 expanded)
%              Number of equality atoms :   50 ( 206 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_42,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_188,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_196,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_188])).

tff(c_40,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_201,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_40])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_571,plain,(
    ! [A_152,B_150,E_151,F_155,C_153,D_154] :
      ( k1_funct_1(k8_funct_2(B_150,C_153,A_152,D_154,E_151),F_155) = k1_funct_1(E_151,k1_funct_1(D_154,F_155))
      | k1_xboole_0 = B_150
      | ~ r1_tarski(k2_relset_1(B_150,C_153,D_154),k1_relset_1(C_153,A_152,E_151))
      | ~ m1_subset_1(F_155,B_150)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(C_153,A_152)))
      | ~ v1_funct_1(E_151)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(B_150,C_153)))
      | ~ v1_funct_2(D_154,B_150,C_153)
      | ~ v1_funct_1(D_154)
      | v1_xboole_0(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_573,plain,(
    ! [B_150,D_154,F_155] :
      ( k1_funct_1(k8_funct_2(B_150,'#skF_5','#skF_3',D_154,'#skF_7'),F_155) = k1_funct_1('#skF_7',k1_funct_1(D_154,F_155))
      | k1_xboole_0 = B_150
      | ~ r1_tarski(k2_relset_1(B_150,'#skF_5',D_154),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_155,B_150)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(B_150,'#skF_5')))
      | ~ v1_funct_2(D_154,B_150,'#skF_5')
      | ~ v1_funct_1(D_154)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_571])).

tff(c_580,plain,(
    ! [B_150,D_154,F_155] :
      ( k1_funct_1(k8_funct_2(B_150,'#skF_5','#skF_3',D_154,'#skF_7'),F_155) = k1_funct_1('#skF_7',k1_funct_1(D_154,F_155))
      | k1_xboole_0 = B_150
      | ~ r1_tarski(k2_relset_1(B_150,'#skF_5',D_154),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_155,B_150)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(B_150,'#skF_5')))
      | ~ v1_funct_2(D_154,B_150,'#skF_5')
      | ~ v1_funct_1(D_154)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_573])).

tff(c_604,plain,(
    ! [B_162,D_163,F_164] :
      ( k1_funct_1(k8_funct_2(B_162,'#skF_5','#skF_3',D_163,'#skF_7'),F_164) = k1_funct_1('#skF_7',k1_funct_1(D_163,F_164))
      | k1_xboole_0 = B_162
      | ~ r1_tarski(k2_relset_1(B_162,'#skF_5',D_163),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_164,B_162)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(B_162,'#skF_5')))
      | ~ v1_funct_2(D_163,B_162,'#skF_5')
      | ~ v1_funct_1(D_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_580])).

tff(c_606,plain,(
    ! [F_164] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_164) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_164))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_164,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_201,c_604])).

tff(c_612,plain,(
    ! [F_164] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_164) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_164))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_164,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_606])).

tff(c_613,plain,(
    ! [F_164] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_164) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_164))
      | ~ m1_subset_1(F_164,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_612])).

tff(c_20,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_98,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_95])).

tff(c_104,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_98])).

tff(c_179,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_186,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_179])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_257,plain,(
    ! [A_107,B_108,C_109] :
      ( k7_partfun1(A_107,B_108,C_109) = k1_funct_1(B_108,C_109)
      | ~ r2_hidden(C_109,k1_relat_1(B_108))
      | ~ v1_funct_1(B_108)
      | ~ v5_relat_1(B_108,A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_760,plain,(
    ! [A_187,B_188,A_189] :
      ( k7_partfun1(A_187,B_188,A_189) = k1_funct_1(B_188,A_189)
      | ~ v1_funct_1(B_188)
      | ~ v5_relat_1(B_188,A_187)
      | ~ v1_relat_1(B_188)
      | v1_xboole_0(k1_relat_1(B_188))
      | ~ m1_subset_1(A_189,k1_relat_1(B_188)) ) ),
    inference(resolution,[status(thm)],[c_16,c_257])).

tff(c_764,plain,(
    ! [A_189] :
      ( k7_partfun1('#skF_5','#skF_6',A_189) = k1_funct_1('#skF_6',A_189)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_189,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_186,c_760])).

tff(c_771,plain,(
    ! [A_189] :
      ( k7_partfun1('#skF_5','#skF_6',A_189) = k1_funct_1('#skF_6',A_189)
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_189,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_52,c_764])).

tff(c_782,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_787,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_782,c_12])).

tff(c_195,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_188])).

tff(c_575,plain,(
    ! [B_150,D_154,F_155] :
      ( k1_funct_1(k8_funct_2(B_150,'#skF_4','#skF_5',D_154,'#skF_6'),F_155) = k1_funct_1('#skF_6',k1_funct_1(D_154,F_155))
      | k1_xboole_0 = B_150
      | ~ r1_tarski(k2_relset_1(B_150,'#skF_4',D_154),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_155,B_150)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(B_150,'#skF_4')))
      | ~ v1_funct_2(D_154,B_150,'#skF_4')
      | ~ v1_funct_1(D_154)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_571])).

tff(c_583,plain,(
    ! [B_150,D_154,F_155] :
      ( k1_funct_1(k8_funct_2(B_150,'#skF_4','#skF_5',D_154,'#skF_6'),F_155) = k1_funct_1('#skF_6',k1_funct_1(D_154,F_155))
      | k1_xboole_0 = B_150
      | ~ r1_tarski(k2_relset_1(B_150,'#skF_4',D_154),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_155,B_150)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(B_150,'#skF_4')))
      | ~ v1_funct_2(D_154,B_150,'#skF_4')
      | ~ v1_funct_1(D_154)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_575])).

tff(c_1297,plain,(
    ! [B_150,D_154,F_155] :
      ( k1_funct_1(k8_funct_2(B_150,'#skF_4','#skF_5',D_154,'#skF_6'),F_155) = k1_funct_1('#skF_6',k1_funct_1(D_154,F_155))
      | k1_xboole_0 = B_150
      | ~ r1_tarski(k2_relset_1(B_150,'#skF_4',D_154),k1_xboole_0)
      | ~ m1_subset_1(F_155,B_150)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(k2_zfmisc_1(B_150,'#skF_4')))
      | ~ v1_funct_2(D_154,B_150,'#skF_4')
      | ~ v1_funct_1(D_154)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_583])).

tff(c_1298,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1297])).

tff(c_1301,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1298,c_12])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1301])).

tff(c_1307,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1297])).

tff(c_187,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_179])).

tff(c_101,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_107,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_101])).

tff(c_375,plain,(
    ! [D_127,C_128,A_129,B_130] :
      ( r2_hidden(k1_funct_1(D_127,C_128),k2_relset_1(A_129,B_130,D_127))
      | k1_xboole_0 = B_130
      | ~ r2_hidden(C_128,A_129)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_2(D_127,A_129,B_130)
      | ~ v1_funct_1(D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1208,plain,(
    ! [D_256,A_255,B_254,C_257,B_253] :
      ( r2_hidden(k1_funct_1(D_256,C_257),B_254)
      | ~ r1_tarski(k2_relset_1(A_255,B_253,D_256),B_254)
      | k1_xboole_0 = B_253
      | ~ r2_hidden(C_257,A_255)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_253)))
      | ~ v1_funct_2(D_256,A_255,B_253)
      | ~ v1_funct_1(D_256) ) ),
    inference(resolution,[status(thm)],[c_375,c_6])).

tff(c_1210,plain,(
    ! [C_257] :
      ( r2_hidden(k1_funct_1('#skF_6',C_257),k1_relat_1('#skF_7'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_257,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_201,c_1208])).

tff(c_1219,plain,(
    ! [C_257] :
      ( r2_hidden(k1_funct_1('#skF_6',C_257),k1_relat_1('#skF_7'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_257,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1210])).

tff(c_1222,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1219])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [A_71] :
      ( v1_xboole_0(A_71)
      | r2_hidden('#skF_1'(A_71),A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    ! [A_72] :
      ( ~ r1_tarski(A_72,'#skF_1'(A_72))
      | v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_60,c_22])).

tff(c_74,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_1241,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_74])).

tff(c_1246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1241])).

tff(c_1249,plain,(
    ! [C_258] :
      ( r2_hidden(k1_funct_1('#skF_6',C_258),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_258,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1219])).

tff(c_30,plain,(
    ! [A_27,B_28,C_30] :
      ( k7_partfun1(A_27,B_28,C_30) = k1_funct_1(B_28,C_30)
      | ~ r2_hidden(C_30,k1_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1253,plain,(
    ! [A_27,C_258] :
      ( k7_partfun1(A_27,'#skF_7',k1_funct_1('#skF_6',C_258)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_258))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_27)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_258,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1249,c_30])).

tff(c_1334,plain,(
    ! [A_267,C_268] :
      ( k7_partfun1(A_267,'#skF_7',k1_funct_1('#skF_6',C_268)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_268))
      | ~ v5_relat_1('#skF_7',A_267)
      | ~ r2_hidden(C_268,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_46,c_1253])).

tff(c_36,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1340,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_36])).

tff(c_1346,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_1340])).

tff(c_1361,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1346])).

tff(c_1364,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1361])).

tff(c_1367,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1364])).

tff(c_1369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1307,c_1367])).

tff(c_1370,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1346])).

tff(c_1388,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_1370])).

tff(c_1392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:34:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.73  
% 4.00/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 4.00/1.73  
% 4.00/1.73  %Foreground sorts:
% 4.00/1.73  
% 4.00/1.73  
% 4.00/1.73  %Background operators:
% 4.00/1.73  
% 4.00/1.73  
% 4.00/1.73  %Foreground operators:
% 4.00/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.00/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.00/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.00/1.73  tff('#skF_7', type, '#skF_7': $i).
% 4.00/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.73  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.00/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.00/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.00/1.73  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.00/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.00/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.00/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.00/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.00/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.00/1.73  tff('#skF_8', type, '#skF_8': $i).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.00/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.00/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.00/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.00/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.00/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.00/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.00/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/1.73  
% 4.32/1.75  tff(f_146, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 4.32/1.75  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.32/1.75  tff(f_109, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 4.32/1.75  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.32/1.75  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.32/1.75  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.32/1.75  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.32/1.75  tff(f_85, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 4.32/1.75  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.32/1.75  tff(f_121, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 4.32/1.75  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.32/1.75  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.32/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.32/1.75  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.32/1.75  tff(c_42, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_188, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.32/1.75  tff(c_196, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_188])).
% 4.32/1.75  tff(c_40, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_201, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_40])).
% 4.32/1.75  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_46, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_571, plain, (![A_152, B_150, E_151, F_155, C_153, D_154]: (k1_funct_1(k8_funct_2(B_150, C_153, A_152, D_154, E_151), F_155)=k1_funct_1(E_151, k1_funct_1(D_154, F_155)) | k1_xboole_0=B_150 | ~r1_tarski(k2_relset_1(B_150, C_153, D_154), k1_relset_1(C_153, A_152, E_151)) | ~m1_subset_1(F_155, B_150) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(C_153, A_152))) | ~v1_funct_1(E_151) | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(B_150, C_153))) | ~v1_funct_2(D_154, B_150, C_153) | ~v1_funct_1(D_154) | v1_xboole_0(C_153))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.32/1.75  tff(c_573, plain, (![B_150, D_154, F_155]: (k1_funct_1(k8_funct_2(B_150, '#skF_5', '#skF_3', D_154, '#skF_7'), F_155)=k1_funct_1('#skF_7', k1_funct_1(D_154, F_155)) | k1_xboole_0=B_150 | ~r1_tarski(k2_relset_1(B_150, '#skF_5', D_154), k1_relat_1('#skF_7')) | ~m1_subset_1(F_155, B_150) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(B_150, '#skF_5'))) | ~v1_funct_2(D_154, B_150, '#skF_5') | ~v1_funct_1(D_154) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_571])).
% 4.32/1.75  tff(c_580, plain, (![B_150, D_154, F_155]: (k1_funct_1(k8_funct_2(B_150, '#skF_5', '#skF_3', D_154, '#skF_7'), F_155)=k1_funct_1('#skF_7', k1_funct_1(D_154, F_155)) | k1_xboole_0=B_150 | ~r1_tarski(k2_relset_1(B_150, '#skF_5', D_154), k1_relat_1('#skF_7')) | ~m1_subset_1(F_155, B_150) | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(B_150, '#skF_5'))) | ~v1_funct_2(D_154, B_150, '#skF_5') | ~v1_funct_1(D_154) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_573])).
% 4.32/1.75  tff(c_604, plain, (![B_162, D_163, F_164]: (k1_funct_1(k8_funct_2(B_162, '#skF_5', '#skF_3', D_163, '#skF_7'), F_164)=k1_funct_1('#skF_7', k1_funct_1(D_163, F_164)) | k1_xboole_0=B_162 | ~r1_tarski(k2_relset_1(B_162, '#skF_5', D_163), k1_relat_1('#skF_7')) | ~m1_subset_1(F_164, B_162) | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(B_162, '#skF_5'))) | ~v1_funct_2(D_163, B_162, '#skF_5') | ~v1_funct_1(D_163))), inference(negUnitSimplification, [status(thm)], [c_54, c_580])).
% 4.32/1.75  tff(c_606, plain, (![F_164]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_164)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_164)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_164, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_201, c_604])).
% 4.32/1.75  tff(c_612, plain, (![F_164]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_164)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_164)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_164, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_606])).
% 4.32/1.75  tff(c_613, plain, (![F_164]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_164)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_164)) | ~m1_subset_1(F_164, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_612])).
% 4.32/1.75  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.32/1.75  tff(c_95, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.32/1.75  tff(c_98, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_95])).
% 4.32/1.75  tff(c_104, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_98])).
% 4.32/1.75  tff(c_179, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.32/1.75  tff(c_186, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_179])).
% 4.32/1.75  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.32/1.75  tff(c_257, plain, (![A_107, B_108, C_109]: (k7_partfun1(A_107, B_108, C_109)=k1_funct_1(B_108, C_109) | ~r2_hidden(C_109, k1_relat_1(B_108)) | ~v1_funct_1(B_108) | ~v5_relat_1(B_108, A_107) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.32/1.75  tff(c_760, plain, (![A_187, B_188, A_189]: (k7_partfun1(A_187, B_188, A_189)=k1_funct_1(B_188, A_189) | ~v1_funct_1(B_188) | ~v5_relat_1(B_188, A_187) | ~v1_relat_1(B_188) | v1_xboole_0(k1_relat_1(B_188)) | ~m1_subset_1(A_189, k1_relat_1(B_188)))), inference(resolution, [status(thm)], [c_16, c_257])).
% 4.32/1.75  tff(c_764, plain, (![A_189]: (k7_partfun1('#skF_5', '#skF_6', A_189)=k1_funct_1('#skF_6', A_189) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_189, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_186, c_760])).
% 4.32/1.75  tff(c_771, plain, (![A_189]: (k7_partfun1('#skF_5', '#skF_6', A_189)=k1_funct_1('#skF_6', A_189) | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_189, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_52, c_764])).
% 4.32/1.75  tff(c_782, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_771])).
% 4.32/1.75  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.32/1.75  tff(c_787, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_782, c_12])).
% 4.32/1.75  tff(c_195, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_188])).
% 4.32/1.75  tff(c_575, plain, (![B_150, D_154, F_155]: (k1_funct_1(k8_funct_2(B_150, '#skF_4', '#skF_5', D_154, '#skF_6'), F_155)=k1_funct_1('#skF_6', k1_funct_1(D_154, F_155)) | k1_xboole_0=B_150 | ~r1_tarski(k2_relset_1(B_150, '#skF_4', D_154), k1_relat_1('#skF_6')) | ~m1_subset_1(F_155, B_150) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(B_150, '#skF_4'))) | ~v1_funct_2(D_154, B_150, '#skF_4') | ~v1_funct_1(D_154) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_571])).
% 4.32/1.75  tff(c_583, plain, (![B_150, D_154, F_155]: (k1_funct_1(k8_funct_2(B_150, '#skF_4', '#skF_5', D_154, '#skF_6'), F_155)=k1_funct_1('#skF_6', k1_funct_1(D_154, F_155)) | k1_xboole_0=B_150 | ~r1_tarski(k2_relset_1(B_150, '#skF_4', D_154), k1_relat_1('#skF_6')) | ~m1_subset_1(F_155, B_150) | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(B_150, '#skF_4'))) | ~v1_funct_2(D_154, B_150, '#skF_4') | ~v1_funct_1(D_154) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_575])).
% 4.32/1.75  tff(c_1297, plain, (![B_150, D_154, F_155]: (k1_funct_1(k8_funct_2(B_150, '#skF_4', '#skF_5', D_154, '#skF_6'), F_155)=k1_funct_1('#skF_6', k1_funct_1(D_154, F_155)) | k1_xboole_0=B_150 | ~r1_tarski(k2_relset_1(B_150, '#skF_4', D_154), k1_xboole_0) | ~m1_subset_1(F_155, B_150) | ~m1_subset_1(D_154, k1_zfmisc_1(k2_zfmisc_1(B_150, '#skF_4'))) | ~v1_funct_2(D_154, B_150, '#skF_4') | ~v1_funct_1(D_154) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_583])).
% 4.32/1.75  tff(c_1298, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1297])).
% 4.32/1.75  tff(c_1301, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1298, c_12])).
% 4.32/1.75  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1301])).
% 4.32/1.75  tff(c_1307, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1297])).
% 4.32/1.75  tff(c_187, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_179])).
% 4.32/1.75  tff(c_101, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_95])).
% 4.32/1.75  tff(c_107, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_101])).
% 4.32/1.75  tff(c_375, plain, (![D_127, C_128, A_129, B_130]: (r2_hidden(k1_funct_1(D_127, C_128), k2_relset_1(A_129, B_130, D_127)) | k1_xboole_0=B_130 | ~r2_hidden(C_128, A_129) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_2(D_127, A_129, B_130) | ~v1_funct_1(D_127))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.32/1.75  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.32/1.75  tff(c_1208, plain, (![D_256, A_255, B_254, C_257, B_253]: (r2_hidden(k1_funct_1(D_256, C_257), B_254) | ~r1_tarski(k2_relset_1(A_255, B_253, D_256), B_254) | k1_xboole_0=B_253 | ~r2_hidden(C_257, A_255) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_253))) | ~v1_funct_2(D_256, A_255, B_253) | ~v1_funct_1(D_256))), inference(resolution, [status(thm)], [c_375, c_6])).
% 4.32/1.75  tff(c_1210, plain, (![C_257]: (r2_hidden(k1_funct_1('#skF_6', C_257), k1_relat_1('#skF_7')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_257, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_201, c_1208])).
% 4.32/1.75  tff(c_1219, plain, (![C_257]: (r2_hidden(k1_funct_1('#skF_6', C_257), k1_relat_1('#skF_7')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_257, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1210])).
% 4.32/1.75  tff(c_1222, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1219])).
% 4.32/1.75  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.32/1.75  tff(c_60, plain, (![A_71]: (v1_xboole_0(A_71) | r2_hidden('#skF_1'(A_71), A_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.32/1.75  tff(c_22, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.32/1.75  tff(c_69, plain, (![A_72]: (~r1_tarski(A_72, '#skF_1'(A_72)) | v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_60, c_22])).
% 4.32/1.75  tff(c_74, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_69])).
% 4.32/1.75  tff(c_1241, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_74])).
% 4.32/1.75  tff(c_1246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1241])).
% 4.32/1.75  tff(c_1249, plain, (![C_258]: (r2_hidden(k1_funct_1('#skF_6', C_258), k1_relat_1('#skF_7')) | ~r2_hidden(C_258, '#skF_4'))), inference(splitRight, [status(thm)], [c_1219])).
% 4.32/1.75  tff(c_30, plain, (![A_27, B_28, C_30]: (k7_partfun1(A_27, B_28, C_30)=k1_funct_1(B_28, C_30) | ~r2_hidden(C_30, k1_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.32/1.75  tff(c_1253, plain, (![A_27, C_258]: (k7_partfun1(A_27, '#skF_7', k1_funct_1('#skF_6', C_258))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_258)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_27) | ~v1_relat_1('#skF_7') | ~r2_hidden(C_258, '#skF_4'))), inference(resolution, [status(thm)], [c_1249, c_30])).
% 4.32/1.75  tff(c_1334, plain, (![A_267, C_268]: (k7_partfun1(A_267, '#skF_7', k1_funct_1('#skF_6', C_268))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_268)) | ~v5_relat_1('#skF_7', A_267) | ~r2_hidden(C_268, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_46, c_1253])).
% 4.32/1.75  tff(c_36, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.32/1.75  tff(c_1340, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1334, c_36])).
% 4.32/1.75  tff(c_1346, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_1340])).
% 4.32/1.75  tff(c_1361, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_1346])).
% 4.32/1.75  tff(c_1364, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_1361])).
% 4.32/1.75  tff(c_1367, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1364])).
% 4.32/1.75  tff(c_1369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1307, c_1367])).
% 4.32/1.75  tff(c_1370, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_1346])).
% 4.32/1.75  tff(c_1388, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_613, c_1370])).
% 4.32/1.75  tff(c_1392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1388])).
% 4.32/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.75  
% 4.32/1.75  Inference rules
% 4.32/1.75  ----------------------
% 4.32/1.75  #Ref     : 0
% 4.32/1.75  #Sup     : 281
% 4.32/1.75  #Fact    : 0
% 4.32/1.75  #Define  : 0
% 4.32/1.75  #Split   : 14
% 4.32/1.75  #Chain   : 0
% 4.32/1.75  #Close   : 0
% 4.32/1.75  
% 4.32/1.75  Ordering : KBO
% 4.32/1.75  
% 4.32/1.75  Simplification rules
% 4.32/1.75  ----------------------
% 4.32/1.75  #Subsume      : 106
% 4.32/1.75  #Demod        : 152
% 4.32/1.75  #Tautology    : 62
% 4.32/1.75  #SimpNegUnit  : 23
% 4.32/1.75  #BackRed      : 38
% 4.32/1.75  
% 4.32/1.75  #Partial instantiations: 0
% 4.32/1.75  #Strategies tried      : 1
% 4.32/1.75  
% 4.32/1.75  Timing (in seconds)
% 4.32/1.75  ----------------------
% 4.32/1.76  Preprocessing        : 0.35
% 4.32/1.76  Parsing              : 0.19
% 4.32/1.76  CNF conversion       : 0.03
% 4.32/1.76  Main loop            : 0.55
% 4.32/1.76  Inferencing          : 0.19
% 4.32/1.76  Reduction            : 0.17
% 4.32/1.76  Demodulation         : 0.11
% 4.32/1.76  BG Simplification    : 0.03
% 4.32/1.76  Subsumption          : 0.13
% 4.32/1.76  Abstraction          : 0.03
% 4.32/1.76  MUC search           : 0.00
% 4.32/1.76  Cooper               : 0.00
% 4.32/1.76  Total                : 0.95
% 4.32/1.76  Index Insertion      : 0.00
% 4.32/1.76  Index Deletion       : 0.00
% 4.32/1.76  Index Matching       : 0.00
% 4.32/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
