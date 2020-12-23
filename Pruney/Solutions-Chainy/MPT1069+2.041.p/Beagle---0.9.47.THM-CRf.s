%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:51 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 277 expanded)
%              Number of leaves         :   42 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          :  240 (1032 expanded)
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

tff(f_141,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
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

tff(f_80,axiom,(
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

tff(f_116,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_181,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_188,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_181])).

tff(c_38,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_190,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_38])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_570,plain,(
    ! [C_152,D_151,F_148,B_149,A_150,E_153] :
      ( k1_funct_1(k8_funct_2(B_149,C_152,A_150,D_151,E_153),F_148) = k1_funct_1(E_153,k1_funct_1(D_151,F_148))
      | k1_xboole_0 = B_149
      | ~ r1_tarski(k2_relset_1(B_149,C_152,D_151),k1_relset_1(C_152,A_150,E_153))
      | ~ m1_subset_1(F_148,B_149)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(C_152,A_150)))
      | ~ v1_funct_1(E_153)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_149,C_152)))
      | ~ v1_funct_2(D_151,B_149,C_152)
      | ~ v1_funct_1(D_151)
      | v1_xboole_0(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_574,plain,(
    ! [B_149,D_151,F_148] :
      ( k1_funct_1(k8_funct_2(B_149,'#skF_5','#skF_3',D_151,'#skF_7'),F_148) = k1_funct_1('#skF_7',k1_funct_1(D_151,F_148))
      | k1_xboole_0 = B_149
      | ~ r1_tarski(k2_relset_1(B_149,'#skF_5',D_151),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_148,B_149)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_149,'#skF_5')))
      | ~ v1_funct_2(D_151,B_149,'#skF_5')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_570])).

tff(c_581,plain,(
    ! [B_149,D_151,F_148] :
      ( k1_funct_1(k8_funct_2(B_149,'#skF_5','#skF_3',D_151,'#skF_7'),F_148) = k1_funct_1('#skF_7',k1_funct_1(D_151,F_148))
      | k1_xboole_0 = B_149
      | ~ r1_tarski(k2_relset_1(B_149,'#skF_5',D_151),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_148,B_149)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_149,'#skF_5')))
      | ~ v1_funct_2(D_151,B_149,'#skF_5')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_574])).

tff(c_620,plain,(
    ! [B_161,D_162,F_163] :
      ( k1_funct_1(k8_funct_2(B_161,'#skF_5','#skF_3',D_162,'#skF_7'),F_163) = k1_funct_1('#skF_7',k1_funct_1(D_162,F_163))
      | k1_xboole_0 = B_161
      | ~ r1_tarski(k2_relset_1(B_161,'#skF_5',D_162),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_163,B_161)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(B_161,'#skF_5')))
      | ~ v1_funct_2(D_162,B_161,'#skF_5')
      | ~ v1_funct_1(D_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_581])).

tff(c_622,plain,(
    ! [F_163] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_163) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_163))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_163,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_190,c_620])).

tff(c_628,plain,(
    ! [F_163] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_163) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_163))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_163,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_622])).

tff(c_629,plain,(
    ! [F_163] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_163) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_163))
      | ~ m1_subset_1(F_163,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_628])).

tff(c_86,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_86])).

tff(c_162,plain,(
    ! [C_89,B_90,A_91] :
      ( v5_relat_1(C_89,B_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_170,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_162])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_236,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_partfun1(A_102,B_103,C_104) = k1_funct_1(B_103,C_104)
      | ~ r2_hidden(C_104,k1_relat_1(B_103))
      | ~ v1_funct_1(B_103)
      | ~ v5_relat_1(B_103,A_102)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_763,plain,(
    ! [A_186,B_187,A_188] :
      ( k7_partfun1(A_186,B_187,A_188) = k1_funct_1(B_187,A_188)
      | ~ v1_funct_1(B_187)
      | ~ v5_relat_1(B_187,A_186)
      | ~ v1_relat_1(B_187)
      | v1_xboole_0(k1_relat_1(B_187))
      | ~ m1_subset_1(A_188,k1_relat_1(B_187)) ) ),
    inference(resolution,[status(thm)],[c_16,c_236])).

tff(c_765,plain,(
    ! [A_188] :
      ( k7_partfun1('#skF_5','#skF_6',A_188) = k1_funct_1('#skF_6',A_188)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_188,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_170,c_763])).

tff(c_770,plain,(
    ! [A_188] :
      ( k7_partfun1('#skF_5','#skF_6',A_188) = k1_funct_1('#skF_6',A_188)
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_188,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_50,c_765])).

tff(c_776,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_780,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_776,c_12])).

tff(c_189,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_181])).

tff(c_572,plain,(
    ! [B_149,D_151,F_148] :
      ( k1_funct_1(k8_funct_2(B_149,'#skF_4','#skF_5',D_151,'#skF_6'),F_148) = k1_funct_1('#skF_6',k1_funct_1(D_151,F_148))
      | k1_xboole_0 = B_149
      | ~ r1_tarski(k2_relset_1(B_149,'#skF_4',D_151),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_148,B_149)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_149,'#skF_4')))
      | ~ v1_funct_2(D_151,B_149,'#skF_4')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_570])).

tff(c_579,plain,(
    ! [B_149,D_151,F_148] :
      ( k1_funct_1(k8_funct_2(B_149,'#skF_4','#skF_5',D_151,'#skF_6'),F_148) = k1_funct_1('#skF_6',k1_funct_1(D_151,F_148))
      | k1_xboole_0 = B_149
      | ~ r1_tarski(k2_relset_1(B_149,'#skF_4',D_151),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_148,B_149)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_149,'#skF_4')))
      | ~ v1_funct_2(D_151,B_149,'#skF_4')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_572])).

tff(c_1232,plain,(
    ! [B_149,D_151,F_148] :
      ( k1_funct_1(k8_funct_2(B_149,'#skF_4','#skF_5',D_151,'#skF_6'),F_148) = k1_funct_1('#skF_6',k1_funct_1(D_151,F_148))
      | k1_xboole_0 = B_149
      | ~ r1_tarski(k2_relset_1(B_149,'#skF_4',D_151),k1_xboole_0)
      | ~ m1_subset_1(F_148,B_149)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_149,'#skF_4')))
      | ~ v1_funct_2(D_151,B_149,'#skF_4')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_579])).

tff(c_1233,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1232])).

tff(c_1236,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1233,c_12])).

tff(c_1240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1236])).

tff(c_1242,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_169,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_162])).

tff(c_93,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_368,plain,(
    ! [D_124,C_125,A_126,B_127] :
      ( r2_hidden(k1_funct_1(D_124,C_125),k2_relset_1(A_126,B_127,D_124))
      | k1_xboole_0 = B_127
      | ~ r2_hidden(C_125,A_126)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(D_124,A_126,B_127)
      | ~ v1_funct_1(D_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1076,plain,(
    ! [C_241,D_243,B_244,A_240,B_242] :
      ( r2_hidden(k1_funct_1(D_243,C_241),B_242)
      | ~ r1_tarski(k2_relset_1(A_240,B_244,D_243),B_242)
      | k1_xboole_0 = B_244
      | ~ r2_hidden(C_241,A_240)
      | ~ m1_subset_1(D_243,k1_zfmisc_1(k2_zfmisc_1(A_240,B_244)))
      | ~ v1_funct_2(D_243,A_240,B_244)
      | ~ v1_funct_1(D_243) ) ),
    inference(resolution,[status(thm)],[c_368,c_6])).

tff(c_1078,plain,(
    ! [C_241] :
      ( r2_hidden(k1_funct_1('#skF_6',C_241),k1_relat_1('#skF_7'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_241,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_190,c_1076])).

tff(c_1087,plain,(
    ! [C_241] :
      ( r2_hidden(k1_funct_1('#skF_6',C_241),k1_relat_1('#skF_7'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_241,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1078])).

tff(c_1090,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1087])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [B_66,A_67] :
      ( ~ r1_tarski(B_66,A_67)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_66,plain,(
    ! [A_68] :
      ( ~ r1_tarski(A_68,'#skF_1'(A_68))
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_1108,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_71])).

tff(c_1113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1108])).

tff(c_1125,plain,(
    ! [C_247] :
      ( r2_hidden(k1_funct_1('#skF_6',C_247),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_247,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1087])).

tff(c_28,plain,(
    ! [A_25,B_26,C_28] :
      ( k7_partfun1(A_25,B_26,C_28) = k1_funct_1(B_26,C_28)
      | ~ r2_hidden(C_28,k1_relat_1(B_26))
      | ~ v1_funct_1(B_26)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1129,plain,(
    ! [A_25,C_247] :
      ( k7_partfun1(A_25,'#skF_7',k1_funct_1('#skF_6',C_247)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_247))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_25)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_247,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1125,c_28])).

tff(c_1211,plain,(
    ! [A_261,C_262] :
      ( k7_partfun1(A_261,'#skF_7',k1_funct_1('#skF_6',C_262)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_262))
      | ~ v5_relat_1('#skF_7',A_261)
      | ~ r2_hidden(C_262,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_44,c_1129])).

tff(c_34,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1217,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_34])).

tff(c_1223,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_1217])).

tff(c_1225,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_1228,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1225])).

tff(c_1231,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1228])).

tff(c_1243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1242,c_1231])).

tff(c_1244,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_1303,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_1244])).

tff(c_1307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.63  
% 3.86/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 3.86/1.63  
% 3.86/1.63  %Foreground sorts:
% 3.86/1.63  
% 3.86/1.63  
% 3.86/1.63  %Background operators:
% 3.86/1.63  
% 3.86/1.63  
% 3.86/1.63  %Foreground operators:
% 3.86/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.86/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.86/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.86/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.63  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.86/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.86/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.86/1.63  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.86/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.86/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.86/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.86/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.86/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.86/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.86/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.86/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.86/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.86/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.63  
% 3.86/1.65  tff(f_141, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 3.86/1.65  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.86/1.65  tff(f_104, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.86/1.65  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.86/1.65  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.86/1.65  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.86/1.65  tff(f_80, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.86/1.65  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.86/1.65  tff(f_116, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.86/1.65  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.86/1.65  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.86/1.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.86/1.65  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.86/1.65  tff(c_40, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_181, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.86/1.65  tff(c_188, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_181])).
% 3.86/1.65  tff(c_38, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_190, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_38])).
% 3.86/1.65  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_570, plain, (![C_152, D_151, F_148, B_149, A_150, E_153]: (k1_funct_1(k8_funct_2(B_149, C_152, A_150, D_151, E_153), F_148)=k1_funct_1(E_153, k1_funct_1(D_151, F_148)) | k1_xboole_0=B_149 | ~r1_tarski(k2_relset_1(B_149, C_152, D_151), k1_relset_1(C_152, A_150, E_153)) | ~m1_subset_1(F_148, B_149) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(C_152, A_150))) | ~v1_funct_1(E_153) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_149, C_152))) | ~v1_funct_2(D_151, B_149, C_152) | ~v1_funct_1(D_151) | v1_xboole_0(C_152))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.86/1.65  tff(c_574, plain, (![B_149, D_151, F_148]: (k1_funct_1(k8_funct_2(B_149, '#skF_5', '#skF_3', D_151, '#skF_7'), F_148)=k1_funct_1('#skF_7', k1_funct_1(D_151, F_148)) | k1_xboole_0=B_149 | ~r1_tarski(k2_relset_1(B_149, '#skF_5', D_151), k1_relat_1('#skF_7')) | ~m1_subset_1(F_148, B_149) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_149, '#skF_5'))) | ~v1_funct_2(D_151, B_149, '#skF_5') | ~v1_funct_1(D_151) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_570])).
% 3.86/1.65  tff(c_581, plain, (![B_149, D_151, F_148]: (k1_funct_1(k8_funct_2(B_149, '#skF_5', '#skF_3', D_151, '#skF_7'), F_148)=k1_funct_1('#skF_7', k1_funct_1(D_151, F_148)) | k1_xboole_0=B_149 | ~r1_tarski(k2_relset_1(B_149, '#skF_5', D_151), k1_relat_1('#skF_7')) | ~m1_subset_1(F_148, B_149) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_149, '#skF_5'))) | ~v1_funct_2(D_151, B_149, '#skF_5') | ~v1_funct_1(D_151) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_574])).
% 3.86/1.65  tff(c_620, plain, (![B_161, D_162, F_163]: (k1_funct_1(k8_funct_2(B_161, '#skF_5', '#skF_3', D_162, '#skF_7'), F_163)=k1_funct_1('#skF_7', k1_funct_1(D_162, F_163)) | k1_xboole_0=B_161 | ~r1_tarski(k2_relset_1(B_161, '#skF_5', D_162), k1_relat_1('#skF_7')) | ~m1_subset_1(F_163, B_161) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(B_161, '#skF_5'))) | ~v1_funct_2(D_162, B_161, '#skF_5') | ~v1_funct_1(D_162))), inference(negUnitSimplification, [status(thm)], [c_52, c_581])).
% 3.86/1.65  tff(c_622, plain, (![F_163]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_163)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_163)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_163, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_190, c_620])).
% 3.86/1.65  tff(c_628, plain, (![F_163]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_163)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_163)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_163, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_622])).
% 3.86/1.65  tff(c_629, plain, (![F_163]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_163)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_163)) | ~m1_subset_1(F_163, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_628])).
% 3.86/1.65  tff(c_86, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.86/1.65  tff(c_94, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_86])).
% 3.86/1.65  tff(c_162, plain, (![C_89, B_90, A_91]: (v5_relat_1(C_89, B_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.86/1.65  tff(c_170, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_162])).
% 3.86/1.65  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.86/1.65  tff(c_236, plain, (![A_102, B_103, C_104]: (k7_partfun1(A_102, B_103, C_104)=k1_funct_1(B_103, C_104) | ~r2_hidden(C_104, k1_relat_1(B_103)) | ~v1_funct_1(B_103) | ~v5_relat_1(B_103, A_102) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.86/1.65  tff(c_763, plain, (![A_186, B_187, A_188]: (k7_partfun1(A_186, B_187, A_188)=k1_funct_1(B_187, A_188) | ~v1_funct_1(B_187) | ~v5_relat_1(B_187, A_186) | ~v1_relat_1(B_187) | v1_xboole_0(k1_relat_1(B_187)) | ~m1_subset_1(A_188, k1_relat_1(B_187)))), inference(resolution, [status(thm)], [c_16, c_236])).
% 3.86/1.65  tff(c_765, plain, (![A_188]: (k7_partfun1('#skF_5', '#skF_6', A_188)=k1_funct_1('#skF_6', A_188) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_188, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_170, c_763])).
% 3.86/1.65  tff(c_770, plain, (![A_188]: (k7_partfun1('#skF_5', '#skF_6', A_188)=k1_funct_1('#skF_6', A_188) | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_188, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_50, c_765])).
% 3.86/1.65  tff(c_776, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_770])).
% 3.86/1.65  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.86/1.65  tff(c_780, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_776, c_12])).
% 3.86/1.65  tff(c_189, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_181])).
% 3.86/1.65  tff(c_572, plain, (![B_149, D_151, F_148]: (k1_funct_1(k8_funct_2(B_149, '#skF_4', '#skF_5', D_151, '#skF_6'), F_148)=k1_funct_1('#skF_6', k1_funct_1(D_151, F_148)) | k1_xboole_0=B_149 | ~r1_tarski(k2_relset_1(B_149, '#skF_4', D_151), k1_relat_1('#skF_6')) | ~m1_subset_1(F_148, B_149) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_149, '#skF_4'))) | ~v1_funct_2(D_151, B_149, '#skF_4') | ~v1_funct_1(D_151) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_570])).
% 3.86/1.65  tff(c_579, plain, (![B_149, D_151, F_148]: (k1_funct_1(k8_funct_2(B_149, '#skF_4', '#skF_5', D_151, '#skF_6'), F_148)=k1_funct_1('#skF_6', k1_funct_1(D_151, F_148)) | k1_xboole_0=B_149 | ~r1_tarski(k2_relset_1(B_149, '#skF_4', D_151), k1_relat_1('#skF_6')) | ~m1_subset_1(F_148, B_149) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_149, '#skF_4'))) | ~v1_funct_2(D_151, B_149, '#skF_4') | ~v1_funct_1(D_151) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_572])).
% 3.86/1.65  tff(c_1232, plain, (![B_149, D_151, F_148]: (k1_funct_1(k8_funct_2(B_149, '#skF_4', '#skF_5', D_151, '#skF_6'), F_148)=k1_funct_1('#skF_6', k1_funct_1(D_151, F_148)) | k1_xboole_0=B_149 | ~r1_tarski(k2_relset_1(B_149, '#skF_4', D_151), k1_xboole_0) | ~m1_subset_1(F_148, B_149) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_149, '#skF_4'))) | ~v1_funct_2(D_151, B_149, '#skF_4') | ~v1_funct_1(D_151) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_780, c_579])).
% 3.86/1.65  tff(c_1233, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1232])).
% 3.86/1.65  tff(c_1236, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1233, c_12])).
% 3.86/1.65  tff(c_1240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1236])).
% 3.86/1.65  tff(c_1242, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1232])).
% 3.86/1.65  tff(c_169, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_162])).
% 3.86/1.65  tff(c_93, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_86])).
% 3.86/1.65  tff(c_368, plain, (![D_124, C_125, A_126, B_127]: (r2_hidden(k1_funct_1(D_124, C_125), k2_relset_1(A_126, B_127, D_124)) | k1_xboole_0=B_127 | ~r2_hidden(C_125, A_126) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(D_124, A_126, B_127) | ~v1_funct_1(D_124))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.86/1.65  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.86/1.65  tff(c_1076, plain, (![C_241, D_243, B_244, A_240, B_242]: (r2_hidden(k1_funct_1(D_243, C_241), B_242) | ~r1_tarski(k2_relset_1(A_240, B_244, D_243), B_242) | k1_xboole_0=B_244 | ~r2_hidden(C_241, A_240) | ~m1_subset_1(D_243, k1_zfmisc_1(k2_zfmisc_1(A_240, B_244))) | ~v1_funct_2(D_243, A_240, B_244) | ~v1_funct_1(D_243))), inference(resolution, [status(thm)], [c_368, c_6])).
% 3.86/1.65  tff(c_1078, plain, (![C_241]: (r2_hidden(k1_funct_1('#skF_6', C_241), k1_relat_1('#skF_7')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_241, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_190, c_1076])).
% 3.86/1.65  tff(c_1087, plain, (![C_241]: (r2_hidden(k1_funct_1('#skF_6', C_241), k1_relat_1('#skF_7')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_241, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1078])).
% 3.86/1.65  tff(c_1090, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1087])).
% 3.86/1.65  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.86/1.65  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.65  tff(c_61, plain, (![B_66, A_67]: (~r1_tarski(B_66, A_67) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.86/1.65  tff(c_66, plain, (![A_68]: (~r1_tarski(A_68, '#skF_1'(A_68)) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_4, c_61])).
% 3.86/1.65  tff(c_71, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_66])).
% 3.86/1.65  tff(c_1108, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_71])).
% 3.86/1.65  tff(c_1113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1108])).
% 3.86/1.65  tff(c_1125, plain, (![C_247]: (r2_hidden(k1_funct_1('#skF_6', C_247), k1_relat_1('#skF_7')) | ~r2_hidden(C_247, '#skF_4'))), inference(splitRight, [status(thm)], [c_1087])).
% 3.86/1.65  tff(c_28, plain, (![A_25, B_26, C_28]: (k7_partfun1(A_25, B_26, C_28)=k1_funct_1(B_26, C_28) | ~r2_hidden(C_28, k1_relat_1(B_26)) | ~v1_funct_1(B_26) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.86/1.65  tff(c_1129, plain, (![A_25, C_247]: (k7_partfun1(A_25, '#skF_7', k1_funct_1('#skF_6', C_247))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_247)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_25) | ~v1_relat_1('#skF_7') | ~r2_hidden(C_247, '#skF_4'))), inference(resolution, [status(thm)], [c_1125, c_28])).
% 3.86/1.65  tff(c_1211, plain, (![A_261, C_262]: (k7_partfun1(A_261, '#skF_7', k1_funct_1('#skF_6', C_262))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_262)) | ~v5_relat_1('#skF_7', A_261) | ~r2_hidden(C_262, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_44, c_1129])).
% 3.86/1.65  tff(c_34, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.86/1.65  tff(c_1217, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1211, c_34])).
% 3.86/1.65  tff(c_1223, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_1217])).
% 3.86/1.65  tff(c_1225, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_1223])).
% 3.86/1.65  tff(c_1228, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_1225])).
% 3.86/1.65  tff(c_1231, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1228])).
% 3.86/1.65  tff(c_1243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1242, c_1231])).
% 3.86/1.65  tff(c_1244, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_1223])).
% 3.86/1.65  tff(c_1303, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_629, c_1244])).
% 3.86/1.65  tff(c_1307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1303])).
% 3.86/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.65  
% 3.86/1.65  Inference rules
% 3.86/1.65  ----------------------
% 3.86/1.65  #Ref     : 0
% 3.86/1.65  #Sup     : 266
% 3.86/1.65  #Fact    : 0
% 3.86/1.65  #Define  : 0
% 3.86/1.65  #Split   : 13
% 3.86/1.65  #Chain   : 0
% 3.86/1.65  #Close   : 0
% 3.86/1.65  
% 3.86/1.65  Ordering : KBO
% 3.86/1.65  
% 3.86/1.65  Simplification rules
% 3.86/1.65  ----------------------
% 3.86/1.65  #Subsume      : 95
% 3.86/1.65  #Demod        : 138
% 3.86/1.65  #Tautology    : 57
% 3.86/1.65  #SimpNegUnit  : 17
% 3.86/1.65  #BackRed      : 38
% 3.86/1.65  
% 3.86/1.65  #Partial instantiations: 0
% 3.86/1.65  #Strategies tried      : 1
% 3.86/1.65  
% 3.86/1.65  Timing (in seconds)
% 3.86/1.65  ----------------------
% 3.86/1.65  Preprocessing        : 0.33
% 3.86/1.65  Parsing              : 0.17
% 3.86/1.65  CNF conversion       : 0.03
% 3.86/1.65  Main loop            : 0.53
% 3.86/1.65  Inferencing          : 0.19
% 3.86/1.65  Reduction            : 0.16
% 3.86/1.65  Demodulation         : 0.11
% 3.86/1.65  BG Simplification    : 0.02
% 3.86/1.65  Subsumption          : 0.12
% 3.86/1.65  Abstraction          : 0.03
% 3.86/1.65  MUC search           : 0.00
% 3.86/1.65  Cooper               : 0.00
% 3.86/1.65  Total                : 0.90
% 3.86/1.65  Index Insertion      : 0.00
% 3.86/1.65  Index Deletion       : 0.00
% 3.86/1.65  Index Matching       : 0.00
% 3.86/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
