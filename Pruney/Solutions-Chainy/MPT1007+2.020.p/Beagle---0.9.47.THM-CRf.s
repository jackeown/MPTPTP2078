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
% DateTime   : Thu Dec  3 10:14:13 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.17s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 660 expanded)
%              Number of leaves         :   65 ( 243 expanded)
%              Depth                    :   16
%              Number of atoms          :  202 (1605 expanded)
%              Number of equality atoms :   72 ( 370 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_187,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_67,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_148,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_99,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_175,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_64,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_62,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_78,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_157,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_hidden(B,A)
         => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
            & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_98,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_434,plain,(
    ! [C_127,A_128,B_129] :
      ( v1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_442,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_434])).

tff(c_641,plain,(
    ! [C_153,B_154,A_155] :
      ( v5_relat_1(C_153,B_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_649,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_641])).

tff(c_54,plain,(
    ! [B_59,A_58] :
      ( r1_tarski(k2_relat_1(B_59),A_58)
      | ~ v5_relat_1(B_59,A_58)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_102,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_40,plain,(
    ! [A_45] : ~ v1_xboole_0(k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_821,plain,(
    ! [C_187,A_188,B_189] :
      ( r2_hidden(C_187,A_188)
      | ~ r2_hidden(C_187,B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(A_188)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1012,plain,(
    ! [A_226,B_227,A_228] :
      ( r2_hidden('#skF_1'(A_226,B_227),A_228)
      | ~ m1_subset_1(A_226,k1_zfmisc_1(A_228))
      | r1_tarski(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_8,c_821])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1039,plain,(
    ! [A_229,A_230] :
      ( ~ m1_subset_1(A_229,k1_zfmisc_1(A_230))
      | r1_tarski(A_229,A_230) ) ),
    inference(resolution,[status(thm)],[c_1012,c_6])).

tff(c_1046,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_98,c_1039])).

tff(c_76,plain,(
    ! [A_74] :
      ( r2_hidden('#skF_2'(A_74),A_74)
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_621,plain,(
    ! [C_147,B_148,A_149] :
      ( r2_hidden(C_147,B_148)
      | ~ r2_hidden(C_147,A_149)
      | ~ r1_tarski(A_149,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_742,plain,(
    ! [A_174,B_175] :
      ( r2_hidden('#skF_2'(A_174),B_175)
      | ~ r1_tarski(A_174,B_175)
      | k1_xboole_0 = A_174 ) ),
    inference(resolution,[status(thm)],[c_76,c_621])).

tff(c_72,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_mcart_1(A_71) = B_72
      | ~ r2_hidden(A_71,k2_zfmisc_1(k1_tarski(B_72),C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1072,plain,(
    ! [A_235,B_236,C_237] :
      ( k1_mcart_1('#skF_2'(A_235)) = B_236
      | ~ r1_tarski(A_235,k2_zfmisc_1(k1_tarski(B_236),C_237))
      | k1_xboole_0 = A_235 ) ),
    inference(resolution,[status(thm)],[c_742,c_72])).

tff(c_1092,plain,
    ( k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1046,c_1072])).

tff(c_1098,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1092])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1130,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_96])).

tff(c_100,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    ! [A_50] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_895,plain,(
    ! [A_202,B_203,C_204] :
      ( k1_relset_1(A_202,B_203,C_204) = k1_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_902,plain,(
    ! [A_202,B_203] : k1_relset_1(A_202,B_203,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_895])).

tff(c_905,plain,(
    ! [A_202,B_203] : k1_relset_1(A_202,B_203,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_902])).

tff(c_1106,plain,(
    ! [A_202,B_203] : k1_relset_1(A_202,B_203,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1098,c_905])).

tff(c_1126,plain,(
    ! [A_50] : m1_subset_1('#skF_5',k1_zfmisc_1(A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_44])).

tff(c_92,plain,(
    ! [B_100,A_99,C_101] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_99,B_100,C_101) = A_99
      | ~ v1_funct_2(C_101,A_99,B_100)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1530,plain,(
    ! [B_273,A_274,C_275] :
      ( B_273 = '#skF_5'
      | k1_relset_1(A_274,B_273,C_275) = A_274
      | ~ v1_funct_2(C_275,A_274,B_273)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_274,B_273))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_92])).

tff(c_1535,plain,(
    ! [B_273,A_274] :
      ( B_273 = '#skF_5'
      | k1_relset_1(A_274,B_273,'#skF_5') = A_274
      | ~ v1_funct_2('#skF_5',A_274,B_273) ) ),
    inference(resolution,[status(thm)],[c_1126,c_1530])).

tff(c_1747,plain,(
    ! [B_307,A_308] :
      ( B_307 = '#skF_5'
      | A_308 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_308,B_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_1535])).

tff(c_1756,plain,
    ( '#skF_5' = '#skF_4'
    | k1_tarski('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_100,c_1747])).

tff(c_1763,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1130,c_1756])).

tff(c_38,plain,(
    ! [A_44] : k3_tarski(k1_tarski(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1787,plain,(
    k3_tarski('#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_38])).

tff(c_36,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1129,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1098,c_36])).

tff(c_1800,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_1129])).

tff(c_1829,plain,(
    ! [A_50] : m1_subset_1('#skF_3',k1_zfmisc_1(A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_1126])).

tff(c_48,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(A_53,B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_275,plain,(
    ! [A_115,B_116] : k1_setfam_1(k2_tarski(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_324,plain,(
    ! [B_122,A_123] : k1_setfam_1(k2_tarski(B_122,A_123)) = k3_xboole_0(A_123,B_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_275])).

tff(c_46,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_350,plain,(
    ! [B_124,A_125] : k3_xboole_0(B_124,A_125) = k3_xboole_0(A_125,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_46])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_366,plain,(
    ! [A_125] : k3_xboole_0(k1_xboole_0,A_125) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_12])).

tff(c_458,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k3_xboole_0(A_135,B_136)) = k4_xboole_0(A_135,B_136) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_187,plain,(
    ! [B_111,A_112] : k5_xboole_0(B_111,A_112) = k5_xboole_0(A_112,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_203,plain,(
    ! [A_112] : k5_xboole_0(k1_xboole_0,A_112) = A_112 ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_14])).

tff(c_465,plain,(
    ! [B_136] : k4_xboole_0(k1_xboole_0,B_136) = k3_xboole_0(k1_xboole_0,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_203])).

tff(c_489,plain,(
    ! [B_136] : k4_xboole_0(k1_xboole_0,B_136) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_465])).

tff(c_1117,plain,(
    ! [B_136] : k4_xboole_0('#skF_5',B_136) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1098,c_489])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden(A_42,B_43)
      | k4_xboole_0(k1_tarski(A_42),B_43) != k1_tarski(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1775,plain,(
    ! [B_43] :
      ( ~ r2_hidden('#skF_3',B_43)
      | k4_xboole_0('#skF_5',B_43) != k1_tarski('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_32])).

tff(c_1794,plain,(
    ! [B_309] : ~ r2_hidden('#skF_3',B_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1763,c_1117,c_1775])).

tff(c_2344,plain,(
    ! [B_343] :
      ( v1_xboole_0(B_343)
      | ~ m1_subset_1('#skF_3',B_343) ) ),
    inference(resolution,[status(thm)],[c_48,c_1794])).

tff(c_2347,plain,(
    ! [A_50] : v1_xboole_0(k1_zfmisc_1(A_50)) ),
    inference(resolution,[status(thm)],[c_1829,c_2344])).

tff(c_2351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2347])).

tff(c_2353,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1092])).

tff(c_2352,plain,(
    k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1092])).

tff(c_80,plain,(
    ! [B_98,A_96] :
      ( r2_hidden(k1_mcart_1(B_98),k1_relat_1(A_96))
      | ~ r2_hidden(B_98,A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2361,plain,(
    ! [A_344] :
      ( r2_hidden('#skF_3',k1_relat_1(A_344))
      | ~ r2_hidden('#skF_2'('#skF_5'),A_344)
      | ~ v1_relat_1(A_344) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_80])).

tff(c_2377,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_76,c_2361])).

tff(c_2387,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_2377])).

tff(c_2388,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2353,c_2387])).

tff(c_2389,plain,(
    ! [B_345,A_346] :
      ( r2_hidden(k1_funct_1(B_345,A_346),k2_relat_1(B_345))
      | ~ r2_hidden(A_346,k1_relat_1(B_345))
      | ~ v1_funct_1(B_345)
      | ~ v1_relat_1(B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4099,plain,(
    ! [B_534,A_535,B_536] :
      ( r2_hidden(k1_funct_1(B_534,A_535),B_536)
      | ~ r1_tarski(k2_relat_1(B_534),B_536)
      | ~ r2_hidden(A_535,k1_relat_1(B_534))
      | ~ v1_funct_1(B_534)
      | ~ v1_relat_1(B_534) ) ),
    inference(resolution,[status(thm)],[c_2389,c_4])).

tff(c_94,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_4133,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4099,c_94])).

tff(c_4146,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_102,c_2388,c_4133])).

tff(c_4152,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_4146])).

tff(c_4159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_649,c_4152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.14  
% 6.06/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.14  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 6.06/2.14  
% 6.06/2.14  %Foreground sorts:
% 6.06/2.14  
% 6.06/2.14  
% 6.06/2.14  %Background operators:
% 6.06/2.14  
% 6.06/2.14  
% 6.06/2.14  %Foreground operators:
% 6.06/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.06/2.14  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.06/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.06/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.06/2.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.06/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.06/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.06/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.06/2.14  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.06/2.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.06/2.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.06/2.14  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.06/2.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.06/2.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.06/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.06/2.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.06/2.14  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.14  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.06/2.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.06/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.06/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.06/2.14  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.14  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.06/2.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.06/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.06/2.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.06/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.06/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.06/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.06/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.06/2.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.06/2.14  
% 6.17/2.16  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 6.17/2.16  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.17/2.16  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.17/2.16  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.17/2.16  tff(f_67, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.17/2.16  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.17/2.16  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.17/2.16  tff(f_148, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 6.17/2.16  tff(f_127, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 6.17/2.16  tff(f_99, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.17/2.16  tff(f_76, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.17/2.16  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.17/2.16  tff(f_175, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.17/2.16  tff(f_64, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 6.17/2.16  tff(f_62, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 6.17/2.16  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.17/2.16  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.17/2.16  tff(f_78, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.17/2.16  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.17/2.16  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.17/2.16  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.17/2.16  tff(f_40, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.17/2.16  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 6.17/2.16  tff(f_157, axiom, (![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_mcart_1)).
% 6.17/2.16  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 6.17/2.16  tff(c_98, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.17/2.16  tff(c_434, plain, (![C_127, A_128, B_129]: (v1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.17/2.16  tff(c_442, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_98, c_434])).
% 6.17/2.16  tff(c_641, plain, (![C_153, B_154, A_155]: (v5_relat_1(C_153, B_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.17/2.16  tff(c_649, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_98, c_641])).
% 6.17/2.16  tff(c_54, plain, (![B_59, A_58]: (r1_tarski(k2_relat_1(B_59), A_58) | ~v5_relat_1(B_59, A_58) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.17/2.16  tff(c_102, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.17/2.16  tff(c_40, plain, (![A_45]: (~v1_xboole_0(k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.17/2.16  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.17/2.16  tff(c_821, plain, (![C_187, A_188, B_189]: (r2_hidden(C_187, A_188) | ~r2_hidden(C_187, B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(A_188)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.17/2.16  tff(c_1012, plain, (![A_226, B_227, A_228]: (r2_hidden('#skF_1'(A_226, B_227), A_228) | ~m1_subset_1(A_226, k1_zfmisc_1(A_228)) | r1_tarski(A_226, B_227))), inference(resolution, [status(thm)], [c_8, c_821])).
% 6.17/2.16  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.17/2.16  tff(c_1039, plain, (![A_229, A_230]: (~m1_subset_1(A_229, k1_zfmisc_1(A_230)) | r1_tarski(A_229, A_230))), inference(resolution, [status(thm)], [c_1012, c_6])).
% 6.17/2.16  tff(c_1046, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_1039])).
% 6.17/2.16  tff(c_76, plain, (![A_74]: (r2_hidden('#skF_2'(A_74), A_74) | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.17/2.16  tff(c_621, plain, (![C_147, B_148, A_149]: (r2_hidden(C_147, B_148) | ~r2_hidden(C_147, A_149) | ~r1_tarski(A_149, B_148))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.17/2.16  tff(c_742, plain, (![A_174, B_175]: (r2_hidden('#skF_2'(A_174), B_175) | ~r1_tarski(A_174, B_175) | k1_xboole_0=A_174)), inference(resolution, [status(thm)], [c_76, c_621])).
% 6.17/2.16  tff(c_72, plain, (![A_71, B_72, C_73]: (k1_mcart_1(A_71)=B_72 | ~r2_hidden(A_71, k2_zfmisc_1(k1_tarski(B_72), C_73)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.17/2.16  tff(c_1072, plain, (![A_235, B_236, C_237]: (k1_mcart_1('#skF_2'(A_235))=B_236 | ~r1_tarski(A_235, k2_zfmisc_1(k1_tarski(B_236), C_237)) | k1_xboole_0=A_235)), inference(resolution, [status(thm)], [c_742, c_72])).
% 6.17/2.16  tff(c_1092, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1046, c_1072])).
% 6.17/2.16  tff(c_1098, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1092])).
% 6.17/2.16  tff(c_96, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.17/2.16  tff(c_1130, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_96])).
% 6.17/2.16  tff(c_100, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.17/2.16  tff(c_58, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.17/2.16  tff(c_44, plain, (![A_50]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.17/2.16  tff(c_895, plain, (![A_202, B_203, C_204]: (k1_relset_1(A_202, B_203, C_204)=k1_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.17/2.16  tff(c_902, plain, (![A_202, B_203]: (k1_relset_1(A_202, B_203, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_895])).
% 6.17/2.16  tff(c_905, plain, (![A_202, B_203]: (k1_relset_1(A_202, B_203, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_902])).
% 6.17/2.16  tff(c_1106, plain, (![A_202, B_203]: (k1_relset_1(A_202, B_203, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1098, c_905])).
% 6.17/2.16  tff(c_1126, plain, (![A_50]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_44])).
% 6.17/2.16  tff(c_92, plain, (![B_100, A_99, C_101]: (k1_xboole_0=B_100 | k1_relset_1(A_99, B_100, C_101)=A_99 | ~v1_funct_2(C_101, A_99, B_100) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.17/2.16  tff(c_1530, plain, (![B_273, A_274, C_275]: (B_273='#skF_5' | k1_relset_1(A_274, B_273, C_275)=A_274 | ~v1_funct_2(C_275, A_274, B_273) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_274, B_273))))), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_92])).
% 6.17/2.16  tff(c_1535, plain, (![B_273, A_274]: (B_273='#skF_5' | k1_relset_1(A_274, B_273, '#skF_5')=A_274 | ~v1_funct_2('#skF_5', A_274, B_273))), inference(resolution, [status(thm)], [c_1126, c_1530])).
% 6.17/2.16  tff(c_1747, plain, (![B_307, A_308]: (B_307='#skF_5' | A_308='#skF_5' | ~v1_funct_2('#skF_5', A_308, B_307))), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_1535])).
% 6.17/2.16  tff(c_1756, plain, ('#skF_5'='#skF_4' | k1_tarski('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_100, c_1747])).
% 6.17/2.16  tff(c_1763, plain, (k1_tarski('#skF_3')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1130, c_1756])).
% 6.17/2.16  tff(c_38, plain, (![A_44]: (k3_tarski(k1_tarski(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.17/2.16  tff(c_1787, plain, (k3_tarski('#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1763, c_38])).
% 6.17/2.16  tff(c_36, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.17/2.16  tff(c_1129, plain, (k3_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1098, c_36])).
% 6.17/2.16  tff(c_1800, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_1129])).
% 6.17/2.16  tff(c_1829, plain, (![A_50]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_1126])).
% 6.17/2.16  tff(c_48, plain, (![A_53, B_54]: (r2_hidden(A_53, B_54) | v1_xboole_0(B_54) | ~m1_subset_1(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.17/2.16  tff(c_16, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.17/2.16  tff(c_275, plain, (![A_115, B_116]: (k1_setfam_1(k2_tarski(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.17/2.16  tff(c_324, plain, (![B_122, A_123]: (k1_setfam_1(k2_tarski(B_122, A_123))=k3_xboole_0(A_123, B_122))), inference(superposition, [status(thm), theory('equality')], [c_16, c_275])).
% 6.17/2.16  tff(c_46, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.17/2.16  tff(c_350, plain, (![B_124, A_125]: (k3_xboole_0(B_124, A_125)=k3_xboole_0(A_125, B_124))), inference(superposition, [status(thm), theory('equality')], [c_324, c_46])).
% 6.17/2.16  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.17/2.16  tff(c_366, plain, (![A_125]: (k3_xboole_0(k1_xboole_0, A_125)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_350, c_12])).
% 6.17/2.16  tff(c_458, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k3_xboole_0(A_135, B_136))=k4_xboole_0(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.17/2.16  tff(c_187, plain, (![B_111, A_112]: (k5_xboole_0(B_111, A_112)=k5_xboole_0(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.17/2.16  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.17/2.16  tff(c_203, plain, (![A_112]: (k5_xboole_0(k1_xboole_0, A_112)=A_112)), inference(superposition, [status(thm), theory('equality')], [c_187, c_14])).
% 6.17/2.16  tff(c_465, plain, (![B_136]: (k4_xboole_0(k1_xboole_0, B_136)=k3_xboole_0(k1_xboole_0, B_136))), inference(superposition, [status(thm), theory('equality')], [c_458, c_203])).
% 6.17/2.16  tff(c_489, plain, (![B_136]: (k4_xboole_0(k1_xboole_0, B_136)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_366, c_465])).
% 6.17/2.16  tff(c_1117, plain, (![B_136]: (k4_xboole_0('#skF_5', B_136)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1098, c_489])).
% 6.17/2.16  tff(c_32, plain, (![A_42, B_43]: (~r2_hidden(A_42, B_43) | k4_xboole_0(k1_tarski(A_42), B_43)!=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.17/2.16  tff(c_1775, plain, (![B_43]: (~r2_hidden('#skF_3', B_43) | k4_xboole_0('#skF_5', B_43)!=k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1763, c_32])).
% 6.17/2.16  tff(c_1794, plain, (![B_309]: (~r2_hidden('#skF_3', B_309))), inference(demodulation, [status(thm), theory('equality')], [c_1763, c_1117, c_1775])).
% 6.17/2.16  tff(c_2344, plain, (![B_343]: (v1_xboole_0(B_343) | ~m1_subset_1('#skF_3', B_343))), inference(resolution, [status(thm)], [c_48, c_1794])).
% 6.17/2.16  tff(c_2347, plain, (![A_50]: (v1_xboole_0(k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_1829, c_2344])).
% 6.17/2.16  tff(c_2351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2347])).
% 6.17/2.16  tff(c_2353, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_1092])).
% 6.17/2.16  tff(c_2352, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_1092])).
% 6.17/2.16  tff(c_80, plain, (![B_98, A_96]: (r2_hidden(k1_mcart_1(B_98), k1_relat_1(A_96)) | ~r2_hidden(B_98, A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_157])).
% 6.17/2.16  tff(c_2361, plain, (![A_344]: (r2_hidden('#skF_3', k1_relat_1(A_344)) | ~r2_hidden('#skF_2'('#skF_5'), A_344) | ~v1_relat_1(A_344))), inference(superposition, [status(thm), theory('equality')], [c_2352, c_80])).
% 6.17/2.16  tff(c_2377, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_76, c_2361])).
% 6.17/2.16  tff(c_2387, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_2377])).
% 6.17/2.16  tff(c_2388, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2353, c_2387])).
% 6.17/2.16  tff(c_2389, plain, (![B_345, A_346]: (r2_hidden(k1_funct_1(B_345, A_346), k2_relat_1(B_345)) | ~r2_hidden(A_346, k1_relat_1(B_345)) | ~v1_funct_1(B_345) | ~v1_relat_1(B_345))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.17/2.16  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.17/2.16  tff(c_4099, plain, (![B_534, A_535, B_536]: (r2_hidden(k1_funct_1(B_534, A_535), B_536) | ~r1_tarski(k2_relat_1(B_534), B_536) | ~r2_hidden(A_535, k1_relat_1(B_534)) | ~v1_funct_1(B_534) | ~v1_relat_1(B_534))), inference(resolution, [status(thm)], [c_2389, c_4])).
% 6.17/2.16  tff(c_94, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.17/2.16  tff(c_4133, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4099, c_94])).
% 6.17/2.16  tff(c_4146, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_102, c_2388, c_4133])).
% 6.17/2.16  tff(c_4152, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_4146])).
% 6.17/2.16  tff(c_4159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_442, c_649, c_4152])).
% 6.17/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.16  
% 6.17/2.16  Inference rules
% 6.17/2.16  ----------------------
% 6.17/2.16  #Ref     : 0
% 6.17/2.16  #Sup     : 917
% 6.17/2.16  #Fact    : 0
% 6.17/2.16  #Define  : 0
% 6.17/2.16  #Split   : 15
% 6.17/2.16  #Chain   : 0
% 6.17/2.16  #Close   : 0
% 6.17/2.16  
% 6.17/2.16  Ordering : KBO
% 6.17/2.16  
% 6.17/2.16  Simplification rules
% 6.17/2.16  ----------------------
% 6.17/2.16  #Subsume      : 152
% 6.17/2.16  #Demod        : 465
% 6.17/2.16  #Tautology    : 397
% 6.17/2.16  #SimpNegUnit  : 48
% 6.17/2.16  #BackRed      : 93
% 6.17/2.16  
% 6.17/2.16  #Partial instantiations: 0
% 6.17/2.16  #Strategies tried      : 1
% 6.17/2.16  
% 6.17/2.16  Timing (in seconds)
% 6.17/2.16  ----------------------
% 6.17/2.17  Preprocessing        : 0.38
% 6.17/2.17  Parsing              : 0.20
% 6.17/2.17  CNF conversion       : 0.03
% 6.17/2.17  Main loop            : 1.01
% 6.17/2.17  Inferencing          : 0.33
% 6.17/2.17  Reduction            : 0.35
% 6.17/2.17  Demodulation         : 0.25
% 6.17/2.17  BG Simplification    : 0.04
% 6.17/2.17  Subsumption          : 0.20
% 6.17/2.17  Abstraction          : 0.04
% 6.17/2.17  MUC search           : 0.00
% 6.17/2.17  Cooper               : 0.00
% 6.17/2.17  Total                : 1.43
% 6.17/2.17  Index Insertion      : 0.00
% 6.17/2.17  Index Deletion       : 0.00
% 6.17/2.17  Index Matching       : 0.00
% 6.17/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
