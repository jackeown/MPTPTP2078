%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:12 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 297 expanded)
%              Number of leaves         :   50 ( 128 expanded)
%              Depth                    :   12
%              Number of atoms          :  219 ( 796 expanded)
%              Number of equality atoms :   31 (  76 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_181,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_122,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_161,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_62,plain,
    ( ~ v2_funct_2('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_93,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_344,plain,(
    ! [C_93,B_94,A_95] :
      ( ~ v1_xboole_0(C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_358,plain,(
    ! [A_95] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_95,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_344])).

tff(c_451,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_455,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_451])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_74,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_28,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_28])).

tff(c_2593,plain,(
    ! [E_197,F_196,D_195,C_194,A_192,B_193] :
      ( m1_subset_1(k1_partfun1(A_192,B_193,C_194,D_195,E_197,F_196),k1_zfmisc_1(k2_zfmisc_1(A_192,D_195)))
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(C_194,D_195)))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_1(E_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    ! [A_36] : m1_subset_1(k6_relat_1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_77,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44])).

tff(c_64,plain,(
    r2_relset_1('#skF_4','#skF_4',k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k6_partfun1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1335,plain,(
    ! [D_146,C_147,A_148,B_149] :
      ( D_146 = C_147
      | ~ r2_relset_1(A_148,B_149,C_147,D_146)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1345,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_64,c_1335])).

tff(c_1364,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1345])).

tff(c_1619,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1364])).

tff(c_2601,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2593,c_1619])).

tff(c_2638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_2601])).

tff(c_2639,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1364])).

tff(c_5094,plain,(
    ! [B_270,A_269,D_273,E_271,C_272] :
      ( k1_xboole_0 = C_272
      | v2_funct_1(D_273)
      | ~ v2_funct_1(k1_partfun1(A_269,B_270,B_270,C_272,D_273,E_271))
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(B_270,C_272)))
      | ~ v1_funct_2(E_271,B_270,C_272)
      | ~ v1_funct_1(E_271)
      | ~ m1_subset_1(D_273,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ v1_funct_2(D_273,A_269,B_270)
      | ~ v1_funct_1(D_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_5099,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_funct_1('#skF_6')
    | ~ v2_funct_1(k6_partfun1('#skF_4'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2639,c_5094])).

tff(c_5105,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_78,c_5099])).

tff(c_5106,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_5105])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [B_70,A_71] :
      ( ~ r1_tarski(B_70,A_71)
      | ~ r2_hidden(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_131,plain,(
    ! [A_74] :
      ( ~ r1_tarski(A_74,'#skF_1'(A_74))
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_136,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_131])).

tff(c_5161,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5106,c_136])).

tff(c_5167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_455,c_5161])).

tff(c_5170,plain,(
    ! [A_274] : ~ r2_hidden(A_274,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_5175,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_5170])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5186,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5175,c_6])).

tff(c_110,plain,(
    ! [A_68,B_69] :
      ( v1_xboole_0(k2_zfmisc_1(A_68,B_69))
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [A_68,B_69] :
      ( k2_zfmisc_1(A_68,B_69) = k1_xboole_0
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_110,c_6])).

tff(c_145,plain,(
    ! [B_69] : k2_zfmisc_1(k1_xboole_0,B_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_118])).

tff(c_170,plain,(
    ! [A_76] : m1_subset_1(k6_partfun1(A_76),k1_zfmisc_1(k2_zfmisc_1(A_76,A_76))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44])).

tff(c_174,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_170])).

tff(c_346,plain,(
    ! [A_95] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_95,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_174,c_344])).

tff(c_359,plain,(
    ! [A_96] : ~ r2_hidden(A_96,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_346])).

tff(c_364,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_359])).

tff(c_375,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_364,c_6])).

tff(c_390,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_78])).

tff(c_5202,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5186,c_390])).

tff(c_5218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_5202])).

tff(c_5219,plain,(
    ~ v2_funct_2('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_5384,plain,(
    ! [C_294,A_295,B_296] :
      ( v1_relat_1(C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5401,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_5384])).

tff(c_5422,plain,(
    ! [C_301,B_302,A_303] :
      ( v5_relat_1(C_301,B_302)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5440,plain,(
    v5_relat_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_5422])).

tff(c_5899,plain,(
    ! [A_335,B_336,D_337] :
      ( r2_relset_1(A_335,B_336,D_337,D_337)
      | ~ m1_subset_1(D_337,k1_zfmisc_1(k2_zfmisc_1(A_335,B_336))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5910,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_77,c_5899])).

tff(c_5950,plain,(
    ! [A_339,B_340,C_341] :
      ( k2_relset_1(A_339,B_340,C_341) = k2_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5968,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_5950])).

tff(c_50,plain,(
    ! [E_43,F_44,D_42,A_39,C_41,B_40] :
      ( m1_subset_1(k1_partfun1(A_39,B_40,C_41,D_42,E_43,F_44),k1_zfmisc_1(k2_zfmisc_1(A_39,D_42)))
      | ~ m1_subset_1(F_44,k1_zfmisc_1(k2_zfmisc_1(C_41,D_42)))
      | ~ v1_funct_1(F_44)
      | ~ m1_subset_1(E_43,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_1(E_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6213,plain,(
    ! [D_349,C_350,A_351,B_352] :
      ( D_349 = C_350
      | ~ r2_relset_1(A_351,B_352,C_350,D_349)
      | ~ m1_subset_1(D_349,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352)))
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6223,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k6_partfun1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_64,c_6213])).

tff(c_6242,plain,
    ( k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4')
    | ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_6223])).

tff(c_6723,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6242])).

tff(c_7944,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_6723])).

tff(c_7948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_7944])).

tff(c_7949,plain,(
    k1_partfun1('#skF_4','#skF_5','#skF_5','#skF_4','#skF_6','#skF_7') = k6_partfun1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6242])).

tff(c_10361,plain,(
    ! [A_490,B_491,C_492,D_493] :
      ( k2_relset_1(A_490,B_491,C_492) = B_491
      | ~ r2_relset_1(B_491,B_491,k1_partfun1(B_491,A_490,A_490,B_491,D_493,C_492),k6_partfun1(B_491))
      | ~ m1_subset_1(D_493,k1_zfmisc_1(k2_zfmisc_1(B_491,A_490)))
      | ~ v1_funct_2(D_493,B_491,A_490)
      | ~ v1_funct_1(D_493)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ v1_funct_2(C_492,A_490,B_491)
      | ~ v1_funct_1(C_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_10370,plain,
    ( k2_relset_1('#skF_5','#skF_4','#skF_7') = '#skF_4'
    | ~ r2_relset_1('#skF_4','#skF_4',k6_partfun1('#skF_4'),k6_partfun1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7949,c_10361])).

tff(c_10393,plain,(
    k2_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_5910,c_5968,c_10370])).

tff(c_46,plain,(
    ! [B_38] :
      ( v2_funct_2(B_38,k2_relat_1(B_38))
      | ~ v5_relat_1(B_38,k2_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10399,plain,
    ( v2_funct_2('#skF_7',k2_relat_1('#skF_7'))
    | ~ v5_relat_1('#skF_7','#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10393,c_46])).

tff(c_10403,plain,(
    v2_funct_2('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5401,c_5440,c_10393,c_10399])).

tff(c_10405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5219,c_10403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.01/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.01/2.69  
% 8.01/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.01/2.69  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 8.01/2.69  
% 8.01/2.69  %Foreground sorts:
% 8.01/2.69  
% 8.01/2.69  
% 8.01/2.69  %Background operators:
% 8.01/2.69  
% 8.01/2.69  
% 8.01/2.69  %Foreground operators:
% 8.01/2.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.01/2.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.01/2.69  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.01/2.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.01/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.01/2.69  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.01/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.01/2.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.01/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.01/2.69  tff('#skF_7', type, '#skF_7': $i).
% 8.01/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.01/2.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.01/2.69  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.01/2.69  tff('#skF_5', type, '#skF_5': $i).
% 8.01/2.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.01/2.69  tff('#skF_6', type, '#skF_6': $i).
% 8.01/2.69  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.01/2.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.01/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.01/2.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.01/2.69  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.01/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.01/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.01/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.01/2.69  tff('#skF_4', type, '#skF_4': $i).
% 8.01/2.69  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.01/2.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.01/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.01/2.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.01/2.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.01/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.01/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.01/2.69  
% 8.01/2.71  tff(f_181, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 8.01/2.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.01/2.71  tff(f_41, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 8.01/2.71  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 8.01/2.71  tff(f_122, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.01/2.71  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.01/2.71  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.01/2.71  tff(f_100, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 8.01/2.71  tff(f_98, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.01/2.71  tff(f_161, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 8.01/2.71  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.01/2.71  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.01/2.71  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.01/2.71  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.01/2.71  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.01/2.71  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.01/2.71  tff(f_139, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.01/2.71  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 8.01/2.71  tff(c_62, plain, (~v2_funct_2('#skF_7', '#skF_4') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.01/2.71  tff(c_93, plain, (~v2_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_62])).
% 8.01/2.71  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.71  tff(c_10, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.01/2.71  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.01/2.71  tff(c_344, plain, (![C_93, B_94, A_95]: (~v1_xboole_0(C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.01/2.71  tff(c_358, plain, (![A_95]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_95, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_344])).
% 8.01/2.71  tff(c_451, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_358])).
% 8.01/2.71  tff(c_455, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_10, c_451])).
% 8.01/2.71  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.01/2.71  tff(c_74, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.01/2.71  tff(c_70, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.01/2.71  tff(c_68, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.01/2.71  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.01/2.71  tff(c_54, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.01/2.71  tff(c_28, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.01/2.71  tff(c_78, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_28])).
% 8.01/2.71  tff(c_2593, plain, (![E_197, F_196, D_195, C_194, A_192, B_193]: (m1_subset_1(k1_partfun1(A_192, B_193, C_194, D_195, E_197, F_196), k1_zfmisc_1(k2_zfmisc_1(A_192, D_195))) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(C_194, D_195))) | ~v1_funct_1(F_196) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_1(E_197))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.01/2.71  tff(c_44, plain, (![A_36]: (m1_subset_1(k6_relat_1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.01/2.71  tff(c_77, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44])).
% 8.01/2.71  tff(c_64, plain, (r2_relset_1('#skF_4', '#skF_4', k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k6_partfun1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.01/2.71  tff(c_1335, plain, (![D_146, C_147, A_148, B_149]: (D_146=C_147 | ~r2_relset_1(A_148, B_149, C_147, D_146) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.01/2.71  tff(c_1345, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_64, c_1335])).
% 8.01/2.71  tff(c_1364, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1345])).
% 8.01/2.71  tff(c_1619, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1364])).
% 8.01/2.71  tff(c_2601, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_2593, c_1619])).
% 8.01/2.71  tff(c_2638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_2601])).
% 8.01/2.71  tff(c_2639, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4')), inference(splitRight, [status(thm)], [c_1364])).
% 8.01/2.71  tff(c_5094, plain, (![B_270, A_269, D_273, E_271, C_272]: (k1_xboole_0=C_272 | v2_funct_1(D_273) | ~v2_funct_1(k1_partfun1(A_269, B_270, B_270, C_272, D_273, E_271)) | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(B_270, C_272))) | ~v1_funct_2(E_271, B_270, C_272) | ~v1_funct_1(E_271) | ~m1_subset_1(D_273, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~v1_funct_2(D_273, A_269, B_270) | ~v1_funct_1(D_273))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.01/2.71  tff(c_5099, plain, (k1_xboole_0='#skF_4' | v2_funct_1('#skF_6') | ~v2_funct_1(k6_partfun1('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2639, c_5094])).
% 8.01/2.71  tff(c_5105, plain, (k1_xboole_0='#skF_4' | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_78, c_5099])).
% 8.01/2.71  tff(c_5106, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_93, c_5105])).
% 8.01/2.71  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.01/2.71  tff(c_119, plain, (![B_70, A_71]: (~r1_tarski(B_70, A_71) | ~r2_hidden(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.01/2.71  tff(c_131, plain, (![A_74]: (~r1_tarski(A_74, '#skF_1'(A_74)) | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_4, c_119])).
% 8.01/2.71  tff(c_136, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_131])).
% 8.01/2.71  tff(c_5161, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5106, c_136])).
% 8.01/2.71  tff(c_5167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_455, c_5161])).
% 8.01/2.71  tff(c_5170, plain, (![A_274]: (~r2_hidden(A_274, '#skF_6'))), inference(splitRight, [status(thm)], [c_358])).
% 8.01/2.71  tff(c_5175, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_5170])).
% 8.01/2.71  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.01/2.71  tff(c_5186, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_5175, c_6])).
% 8.01/2.71  tff(c_110, plain, (![A_68, B_69]: (v1_xboole_0(k2_zfmisc_1(A_68, B_69)) | ~v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.01/2.71  tff(c_118, plain, (![A_68, B_69]: (k2_zfmisc_1(A_68, B_69)=k1_xboole_0 | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_110, c_6])).
% 8.01/2.71  tff(c_145, plain, (![B_69]: (k2_zfmisc_1(k1_xboole_0, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_136, c_118])).
% 8.01/2.71  tff(c_170, plain, (![A_76]: (m1_subset_1(k6_partfun1(A_76), k1_zfmisc_1(k2_zfmisc_1(A_76, A_76))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44])).
% 8.01/2.71  tff(c_174, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_145, c_170])).
% 8.01/2.71  tff(c_346, plain, (![A_95]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_95, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_174, c_344])).
% 8.01/2.71  tff(c_359, plain, (![A_96]: (~r2_hidden(A_96, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_346])).
% 8.01/2.71  tff(c_364, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_359])).
% 8.01/2.71  tff(c_375, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_364, c_6])).
% 8.01/2.71  tff(c_390, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_375, c_78])).
% 8.01/2.71  tff(c_5202, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5186, c_390])).
% 8.01/2.71  tff(c_5218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_5202])).
% 8.01/2.71  tff(c_5219, plain, (~v2_funct_2('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 8.01/2.71  tff(c_5384, plain, (![C_294, A_295, B_296]: (v1_relat_1(C_294) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.01/2.71  tff(c_5401, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_5384])).
% 8.01/2.71  tff(c_5422, plain, (![C_301, B_302, A_303]: (v5_relat_1(C_301, B_302) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_303, B_302))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.01/2.71  tff(c_5440, plain, (v5_relat_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_5422])).
% 8.01/2.71  tff(c_5899, plain, (![A_335, B_336, D_337]: (r2_relset_1(A_335, B_336, D_337, D_337) | ~m1_subset_1(D_337, k1_zfmisc_1(k2_zfmisc_1(A_335, B_336))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.01/2.71  tff(c_5910, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_77, c_5899])).
% 8.01/2.71  tff(c_5950, plain, (![A_339, B_340, C_341]: (k2_relset_1(A_339, B_340, C_341)=k2_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.01/2.71  tff(c_5968, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_5950])).
% 8.01/2.71  tff(c_50, plain, (![E_43, F_44, D_42, A_39, C_41, B_40]: (m1_subset_1(k1_partfun1(A_39, B_40, C_41, D_42, E_43, F_44), k1_zfmisc_1(k2_zfmisc_1(A_39, D_42))) | ~m1_subset_1(F_44, k1_zfmisc_1(k2_zfmisc_1(C_41, D_42))) | ~v1_funct_1(F_44) | ~m1_subset_1(E_43, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_1(E_43))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.01/2.71  tff(c_6213, plain, (![D_349, C_350, A_351, B_352]: (D_349=C_350 | ~r2_relset_1(A_351, B_352, C_350, D_349) | ~m1_subset_1(D_349, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.01/2.71  tff(c_6223, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k6_partfun1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_64, c_6213])).
% 8.01/2.71  tff(c_6242, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4') | ~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6223])).
% 8.01/2.71  tff(c_6723, plain, (~m1_subset_1(k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_6242])).
% 8.01/2.71  tff(c_7944, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_6723])).
% 8.01/2.71  tff(c_7948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_7944])).
% 8.01/2.71  tff(c_7949, plain, (k1_partfun1('#skF_4', '#skF_5', '#skF_5', '#skF_4', '#skF_6', '#skF_7')=k6_partfun1('#skF_4')), inference(splitRight, [status(thm)], [c_6242])).
% 8.01/2.71  tff(c_10361, plain, (![A_490, B_491, C_492, D_493]: (k2_relset_1(A_490, B_491, C_492)=B_491 | ~r2_relset_1(B_491, B_491, k1_partfun1(B_491, A_490, A_490, B_491, D_493, C_492), k6_partfun1(B_491)) | ~m1_subset_1(D_493, k1_zfmisc_1(k2_zfmisc_1(B_491, A_490))) | ~v1_funct_2(D_493, B_491, A_490) | ~v1_funct_1(D_493) | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~v1_funct_2(C_492, A_490, B_491) | ~v1_funct_1(C_492))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.01/2.71  tff(c_10370, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_7')='#skF_4' | ~r2_relset_1('#skF_4', '#skF_4', k6_partfun1('#skF_4'), k6_partfun1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_7949, c_10361])).
% 8.01/2.71  tff(c_10393, plain, (k2_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_5910, c_5968, c_10370])).
% 8.01/2.71  tff(c_46, plain, (![B_38]: (v2_funct_2(B_38, k2_relat_1(B_38)) | ~v5_relat_1(B_38, k2_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.01/2.71  tff(c_10399, plain, (v2_funct_2('#skF_7', k2_relat_1('#skF_7')) | ~v5_relat_1('#skF_7', '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10393, c_46])).
% 8.01/2.71  tff(c_10403, plain, (v2_funct_2('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5401, c_5440, c_10393, c_10399])).
% 8.01/2.71  tff(c_10405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5219, c_10403])).
% 8.01/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.01/2.71  
% 8.01/2.71  Inference rules
% 8.01/2.71  ----------------------
% 8.01/2.71  #Ref     : 3
% 8.01/2.71  #Sup     : 2530
% 8.01/2.71  #Fact    : 0
% 8.01/2.71  #Define  : 0
% 8.01/2.71  #Split   : 10
% 8.01/2.71  #Chain   : 0
% 8.01/2.71  #Close   : 0
% 8.01/2.71  
% 8.01/2.71  Ordering : KBO
% 8.01/2.71  
% 8.01/2.71  Simplification rules
% 8.01/2.71  ----------------------
% 8.01/2.71  #Subsume      : 250
% 8.01/2.71  #Demod        : 2960
% 8.01/2.71  #Tautology    : 1665
% 8.01/2.71  #SimpNegUnit  : 44
% 8.01/2.71  #BackRed      : 87
% 8.01/2.71  
% 8.01/2.71  #Partial instantiations: 0
% 8.01/2.71  #Strategies tried      : 1
% 8.01/2.71  
% 8.01/2.71  Timing (in seconds)
% 8.01/2.71  ----------------------
% 8.01/2.72  Preprocessing        : 0.39
% 8.01/2.72  Parsing              : 0.20
% 8.01/2.72  CNF conversion       : 0.03
% 8.01/2.72  Main loop            : 1.56
% 8.01/2.72  Inferencing          : 0.50
% 8.01/2.72  Reduction            : 0.55
% 8.01/2.72  Demodulation         : 0.41
% 8.01/2.72  BG Simplification    : 0.06
% 8.01/2.72  Subsumption          : 0.34
% 8.01/2.72  Abstraction          : 0.08
% 8.01/2.72  MUC search           : 0.00
% 8.01/2.72  Cooper               : 0.00
% 8.01/2.72  Total                : 1.99
% 8.01/2.72  Index Insertion      : 0.00
% 8.01/2.72  Index Deletion       : 0.00
% 8.01/2.72  Index Matching       : 0.00
% 8.01/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
