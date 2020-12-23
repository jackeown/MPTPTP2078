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
% DateTime   : Thu Dec  3 10:17:49 EST 2020

% Result     : Theorem 8.43s
% Output     : CNFRefutation 8.43s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 526 expanded)
%              Number of leaves         :   46 ( 200 expanded)
%              Depth                    :   16
%              Number of atoms          :  319 (1841 expanded)
%              Number of equality atoms :   89 ( 404 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(f_199,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_143,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_174,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_155,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_108,axiom,(
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

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_82,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_74,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_84,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_80,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_553,plain,(
    ! [A_148,B_149,C_150] :
      ( k1_relset_1(A_148,B_149,C_150) = k1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_580,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_553])).

tff(c_72,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_584,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_72])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_1619,plain,(
    ! [A_263,C_266,F_261,E_264,B_265,D_262] :
      ( k1_funct_1(k8_funct_2(B_265,C_266,A_263,D_262,E_264),F_261) = k1_funct_1(E_264,k1_funct_1(D_262,F_261))
      | k1_xboole_0 = B_265
      | ~ r1_tarski(k2_relset_1(B_265,C_266,D_262),k1_relset_1(C_266,A_263,E_264))
      | ~ m1_subset_1(F_261,B_265)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(C_266,A_263)))
      | ~ v1_funct_1(E_264)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(B_265,C_266)))
      | ~ v1_funct_2(D_262,B_265,C_266)
      | ~ v1_funct_1(D_262)
      | v1_xboole_0(C_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1627,plain,(
    ! [B_265,D_262,F_261] :
      ( k1_funct_1(k8_funct_2(B_265,'#skF_4','#skF_2',D_262,'#skF_6'),F_261) = k1_funct_1('#skF_6',k1_funct_1(D_262,F_261))
      | k1_xboole_0 = B_265
      | ~ r1_tarski(k2_relset_1(B_265,'#skF_4',D_262),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_261,B_265)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(B_265,'#skF_4')))
      | ~ v1_funct_2(D_262,B_265,'#skF_4')
      | ~ v1_funct_1(D_262)
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_1619])).

tff(c_1637,plain,(
    ! [B_265,D_262,F_261] :
      ( k1_funct_1(k8_funct_2(B_265,'#skF_4','#skF_2',D_262,'#skF_6'),F_261) = k1_funct_1('#skF_6',k1_funct_1(D_262,F_261))
      | k1_xboole_0 = B_265
      | ~ r1_tarski(k2_relset_1(B_265,'#skF_4',D_262),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_261,B_265)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(B_265,'#skF_4')))
      | ~ v1_funct_2(D_262,B_265,'#skF_4')
      | ~ v1_funct_1(D_262)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1627])).

tff(c_1664,plain,(
    ! [B_269,D_270,F_271] :
      ( k1_funct_1(k8_funct_2(B_269,'#skF_4','#skF_2',D_270,'#skF_6'),F_271) = k1_funct_1('#skF_6',k1_funct_1(D_270,F_271))
      | k1_xboole_0 = B_269
      | ~ r1_tarski(k2_relset_1(B_269,'#skF_4',D_270),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_271,B_269)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(B_269,'#skF_4')))
      | ~ v1_funct_2(D_270,B_269,'#skF_4')
      | ~ v1_funct_1(D_270) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1637])).

tff(c_1666,plain,(
    ! [F_271] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_271) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_271))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_271,'#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_584,c_1664])).

tff(c_1669,plain,(
    ! [F_271] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_271) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_271))
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(F_271,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1666])).

tff(c_1670,plain,(
    ! [F_271] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_271) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_271))
      | ~ m1_subset_1(F_271,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1669])).

tff(c_189,plain,(
    ! [C_92,B_93,A_94] :
      ( v5_relat_1(C_92,B_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_211,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_189])).

tff(c_166,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_186,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_166])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_188,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_166])).

tff(c_368,plain,(
    ! [C_118,A_119,B_120] :
      ( v4_relat_1(C_118,A_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_392,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_368])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_234,plain,(
    ! [C_98,B_99,A_100] :
      ( ~ v1_xboole_0(C_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(C_98))
      | ~ r2_hidden(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_460,plain,(
    ! [B_134,A_135,A_136] :
      ( ~ v1_xboole_0(B_134)
      | ~ r2_hidden(A_135,A_136)
      | ~ r1_tarski(A_136,B_134) ) ),
    inference(resolution,[status(thm)],[c_18,c_234])).

tff(c_467,plain,(
    ! [B_137,A_138] :
      ( ~ v1_xboole_0(B_137)
      | ~ r1_tarski(A_138,B_137)
      | k1_xboole_0 = A_138 ) ),
    inference(resolution,[status(thm)],[c_4,c_460])).

tff(c_837,plain,(
    ! [A_180,B_181] :
      ( ~ v1_xboole_0(A_180)
      | k1_relat_1(B_181) = k1_xboole_0
      | ~ v4_relat_1(B_181,A_180)
      | ~ v1_relat_1(B_181) ) ),
    inference(resolution,[status(thm)],[c_26,c_467])).

tff(c_846,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_392,c_837])).

tff(c_857,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_846])).

tff(c_864,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_857])).

tff(c_1420,plain,(
    ! [B_239,D_240,A_241,C_242] :
      ( k1_xboole_0 = B_239
      | v1_funct_2(D_240,A_241,C_242)
      | ~ r1_tarski(k2_relset_1(A_241,B_239,D_240),C_242)
      | ~ m1_subset_1(D_240,k1_zfmisc_1(k2_zfmisc_1(A_241,B_239)))
      | ~ v1_funct_2(D_240,A_241,B_239)
      | ~ v1_funct_1(D_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1422,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3',k1_relat_1('#skF_6'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_584,c_1420])).

tff(c_1425,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1422])).

tff(c_1426,plain,(
    v1_funct_2('#skF_5','#skF_3',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1425])).

tff(c_1529,plain,(
    ! [B_257,D_258,A_259,C_260] :
      ( k1_xboole_0 = B_257
      | m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_259,C_260)))
      | ~ r1_tarski(k2_relset_1(A_259,B_257,D_258),C_260)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_259,B_257)))
      | ~ v1_funct_2(D_258,A_259,B_257)
      | ~ v1_funct_1(D_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1531,plain,
    ( k1_xboole_0 = '#skF_4'
    | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_584,c_1529])).

tff(c_1534,plain,
    ( k1_xboole_0 = '#skF_4'
    | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_1531])).

tff(c_1535,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_1534])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1290,plain,(
    ! [D_224,C_225,B_226,A_227] :
      ( r2_hidden(k1_funct_1(D_224,C_225),B_226)
      | k1_xboole_0 = B_226
      | ~ r2_hidden(C_225,A_227)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226)))
      | ~ v1_funct_2(D_224,A_227,B_226)
      | ~ v1_funct_1(D_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2837,plain,(
    ! [D_344,A_345,B_346,B_347] :
      ( r2_hidden(k1_funct_1(D_344,A_345),B_346)
      | k1_xboole_0 = B_346
      | ~ m1_subset_1(D_344,k1_zfmisc_1(k2_zfmisc_1(B_347,B_346)))
      | ~ v1_funct_2(D_344,B_347,B_346)
      | ~ v1_funct_1(D_344)
      | v1_xboole_0(B_347)
      | ~ m1_subset_1(A_345,B_347) ) ),
    inference(resolution,[status(thm)],[c_14,c_1290])).

tff(c_2842,plain,(
    ! [A_345] :
      ( r2_hidden(k1_funct_1('#skF_5',A_345),k1_relat_1('#skF_6'))
      | k1_relat_1('#skF_6') = k1_xboole_0
      | ~ v1_funct_2('#skF_5','#skF_3',k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_345,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1535,c_2837])).

tff(c_2863,plain,(
    ! [A_345] :
      ( r2_hidden(k1_funct_1('#skF_5',A_345),k1_relat_1('#skF_6'))
      | k1_relat_1('#skF_6') = k1_xboole_0
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_345,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1426,c_2842])).

tff(c_2864,plain,(
    ! [A_345] :
      ( r2_hidden(k1_funct_1('#skF_5',A_345),k1_relat_1('#skF_6'))
      | k1_relat_1('#skF_6') = k1_xboole_0
      | ~ m1_subset_1(A_345,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_864,c_2863])).

tff(c_3295,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2864])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1575,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1535,c_16])).

tff(c_466,plain,(
    ! [B_134,A_1] :
      ( ~ v1_xboole_0(B_134)
      | ~ r1_tarski(A_1,B_134)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_460])).

tff(c_1604,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6')))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1575,c_466])).

tff(c_1618,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1604])).

tff(c_3301,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3295,c_1618])).

tff(c_3315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_3301])).

tff(c_3318,plain,(
    ! [A_360] :
      ( r2_hidden(k1_funct_1('#skF_5',A_360),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_360,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_2864])).

tff(c_50,plain,(
    ! [A_32,B_33,C_35] :
      ( k7_partfun1(A_32,B_33,C_35) = k1_funct_1(B_33,C_35)
      | ~ r2_hidden(C_35,k1_relat_1(B_33))
      | ~ v1_funct_1(B_33)
      | ~ v5_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_3322,plain,(
    ! [A_32,A_360] :
      ( k7_partfun1(A_32,'#skF_6',k1_funct_1('#skF_5',A_360)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_360))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_32)
      | ~ v1_relat_1('#skF_6')
      | ~ m1_subset_1(A_360,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3318,c_50])).

tff(c_6082,plain,(
    ! [A_546,A_547] :
      ( k7_partfun1(A_546,'#skF_6',k1_funct_1('#skF_5',A_547)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',A_547))
      | ~ v5_relat_1('#skF_6',A_546)
      | ~ m1_subset_1(A_547,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_78,c_3322])).

tff(c_68,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_6092,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6082,c_68])).

tff(c_6102,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_211,c_6092])).

tff(c_6107,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1670,c_6102])).

tff(c_6111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6107])).

tff(c_6112,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1604])).

tff(c_6177,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6112,c_70])).

tff(c_582,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_553])).

tff(c_952,plain,(
    ! [B_195,A_196,C_197] :
      ( k1_xboole_0 = B_195
      | k1_relset_1(A_196,B_195,C_197) = A_196
      | ~ v1_funct_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_970,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_952])).

tff(c_985,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_582,c_970])).

tff(c_987,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_985])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_187,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_391,plain,(
    ! [A_119] : v4_relat_1(k1_xboole_0,A_119) ),
    inference(resolution,[status(thm)],[c_12,c_368])).

tff(c_319,plain,(
    ! [B_114,A_115] :
      ( r1_tarski(k1_relat_1(B_114),A_115)
      | ~ v4_relat_1(B_114,A_115)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_119,plain,(
    ! [B_77,A_78] :
      ( ~ r1_tarski(B_77,A_78)
      | ~ r2_hidden(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_123,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_119])).

tff(c_682,plain,(
    ! [B_166] :
      ( k1_relat_1(B_166) = k1_xboole_0
      | ~ v4_relat_1(B_166,'#skF_1'(k1_relat_1(B_166)))
      | ~ v1_relat_1(B_166) ) ),
    inference(resolution,[status(thm)],[c_319,c_123])).

tff(c_690,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_391,c_682])).

tff(c_694,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_690])).

tff(c_6147,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6112,c_6112,c_694])).

tff(c_6178,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_6147])).

tff(c_6185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6177,c_6178])).

tff(c_6186,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1534])).

tff(c_6250,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6186,c_2])).

tff(c_6253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6250])).

tff(c_6254,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1425])).

tff(c_6313,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6254,c_2])).

tff(c_6316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6313])).

tff(c_6317,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_985])).

tff(c_6360,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_2])).

tff(c_6363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6360])).

tff(c_6364,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_857])).

tff(c_6381,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6364,c_582])).

tff(c_6581,plain,(
    ! [B_569,A_570,C_571] :
      ( k1_xboole_0 = B_569
      | k1_relset_1(A_570,B_569,C_571) = A_570
      | ~ v1_funct_2(C_571,A_570,B_569)
      | ~ m1_subset_1(C_571,k1_zfmisc_1(k2_zfmisc_1(A_570,B_569))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6599,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_6581])).

tff(c_6615,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6381,c_6599])).

tff(c_6616,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6615])).

tff(c_6664,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6616,c_2])).

tff(c_6667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.43/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.43/2.74  
% 8.43/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.43/2.74  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 8.43/2.74  
% 8.43/2.74  %Foreground sorts:
% 8.43/2.74  
% 8.43/2.74  
% 8.43/2.74  %Background operators:
% 8.43/2.74  
% 8.43/2.74  
% 8.43/2.74  %Foreground operators:
% 8.43/2.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.43/2.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.43/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.43/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.43/2.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.43/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.43/2.74  tff('#skF_7', type, '#skF_7': $i).
% 8.43/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.43/2.74  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 8.43/2.74  tff('#skF_5', type, '#skF_5': $i).
% 8.43/2.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.43/2.74  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 8.43/2.74  tff('#skF_6', type, '#skF_6': $i).
% 8.43/2.74  tff('#skF_2', type, '#skF_2': $i).
% 8.43/2.74  tff('#skF_3', type, '#skF_3': $i).
% 8.43/2.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.43/2.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.43/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.43/2.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.43/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.43/2.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.43/2.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.43/2.74  tff('#skF_4', type, '#skF_4': $i).
% 8.43/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.43/2.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.43/2.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.43/2.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.43/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.43/2.74  
% 8.43/2.77  tff(f_199, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 8.43/2.77  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.43/2.77  tff(f_143, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 8.43/2.77  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.43/2.77  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.43/2.77  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.43/2.77  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.43/2.77  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.43/2.77  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.43/2.77  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.43/2.77  tff(f_65, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 8.43/2.77  tff(f_174, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 8.43/2.77  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.43/2.77  tff(f_155, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 8.43/2.77  tff(f_119, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 8.43/2.77  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.43/2.77  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.43/2.77  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.43/2.77  tff(c_86, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_70, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_82, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_74, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_84, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_80, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_553, plain, (![A_148, B_149, C_150]: (k1_relset_1(A_148, B_149, C_150)=k1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.43/2.77  tff(c_580, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_553])).
% 8.43/2.77  tff(c_72, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_584, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_72])).
% 8.43/2.77  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_1619, plain, (![A_263, C_266, F_261, E_264, B_265, D_262]: (k1_funct_1(k8_funct_2(B_265, C_266, A_263, D_262, E_264), F_261)=k1_funct_1(E_264, k1_funct_1(D_262, F_261)) | k1_xboole_0=B_265 | ~r1_tarski(k2_relset_1(B_265, C_266, D_262), k1_relset_1(C_266, A_263, E_264)) | ~m1_subset_1(F_261, B_265) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(C_266, A_263))) | ~v1_funct_1(E_264) | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(B_265, C_266))) | ~v1_funct_2(D_262, B_265, C_266) | ~v1_funct_1(D_262) | v1_xboole_0(C_266))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.43/2.77  tff(c_1627, plain, (![B_265, D_262, F_261]: (k1_funct_1(k8_funct_2(B_265, '#skF_4', '#skF_2', D_262, '#skF_6'), F_261)=k1_funct_1('#skF_6', k1_funct_1(D_262, F_261)) | k1_xboole_0=B_265 | ~r1_tarski(k2_relset_1(B_265, '#skF_4', D_262), k1_relat_1('#skF_6')) | ~m1_subset_1(F_261, B_265) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(B_265, '#skF_4'))) | ~v1_funct_2(D_262, B_265, '#skF_4') | ~v1_funct_1(D_262) | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_580, c_1619])).
% 8.43/2.77  tff(c_1637, plain, (![B_265, D_262, F_261]: (k1_funct_1(k8_funct_2(B_265, '#skF_4', '#skF_2', D_262, '#skF_6'), F_261)=k1_funct_1('#skF_6', k1_funct_1(D_262, F_261)) | k1_xboole_0=B_265 | ~r1_tarski(k2_relset_1(B_265, '#skF_4', D_262), k1_relat_1('#skF_6')) | ~m1_subset_1(F_261, B_265) | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(B_265, '#skF_4'))) | ~v1_funct_2(D_262, B_265, '#skF_4') | ~v1_funct_1(D_262) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1627])).
% 8.43/2.77  tff(c_1664, plain, (![B_269, D_270, F_271]: (k1_funct_1(k8_funct_2(B_269, '#skF_4', '#skF_2', D_270, '#skF_6'), F_271)=k1_funct_1('#skF_6', k1_funct_1(D_270, F_271)) | k1_xboole_0=B_269 | ~r1_tarski(k2_relset_1(B_269, '#skF_4', D_270), k1_relat_1('#skF_6')) | ~m1_subset_1(F_271, B_269) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(B_269, '#skF_4'))) | ~v1_funct_2(D_270, B_269, '#skF_4') | ~v1_funct_1(D_270))), inference(negUnitSimplification, [status(thm)], [c_86, c_1637])).
% 8.43/2.77  tff(c_1666, plain, (![F_271]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_271)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_271)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_271, '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_584, c_1664])).
% 8.43/2.77  tff(c_1669, plain, (![F_271]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_271)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_271)) | k1_xboole_0='#skF_3' | ~m1_subset_1(F_271, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1666])).
% 8.43/2.77  tff(c_1670, plain, (![F_271]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_271)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_271)) | ~m1_subset_1(F_271, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1669])).
% 8.43/2.77  tff(c_189, plain, (![C_92, B_93, A_94]: (v5_relat_1(C_92, B_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.43/2.77  tff(c_211, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_189])).
% 8.43/2.77  tff(c_166, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.43/2.77  tff(c_186, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_166])).
% 8.43/2.77  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.43/2.77  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.43/2.77  tff(c_188, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_166])).
% 8.43/2.77  tff(c_368, plain, (![C_118, A_119, B_120]: (v4_relat_1(C_118, A_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.43/2.77  tff(c_392, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_368])).
% 8.43/2.77  tff(c_26, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.43/2.77  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.43/2.77  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.43/2.77  tff(c_234, plain, (![C_98, B_99, A_100]: (~v1_xboole_0(C_98) | ~m1_subset_1(B_99, k1_zfmisc_1(C_98)) | ~r2_hidden(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.43/2.77  tff(c_460, plain, (![B_134, A_135, A_136]: (~v1_xboole_0(B_134) | ~r2_hidden(A_135, A_136) | ~r1_tarski(A_136, B_134))), inference(resolution, [status(thm)], [c_18, c_234])).
% 8.43/2.77  tff(c_467, plain, (![B_137, A_138]: (~v1_xboole_0(B_137) | ~r1_tarski(A_138, B_137) | k1_xboole_0=A_138)), inference(resolution, [status(thm)], [c_4, c_460])).
% 8.43/2.77  tff(c_837, plain, (![A_180, B_181]: (~v1_xboole_0(A_180) | k1_relat_1(B_181)=k1_xboole_0 | ~v4_relat_1(B_181, A_180) | ~v1_relat_1(B_181))), inference(resolution, [status(thm)], [c_26, c_467])).
% 8.43/2.77  tff(c_846, plain, (~v1_xboole_0('#skF_3') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_392, c_837])).
% 8.43/2.77  tff(c_857, plain, (~v1_xboole_0('#skF_3') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_188, c_846])).
% 8.43/2.77  tff(c_864, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_857])).
% 8.43/2.77  tff(c_1420, plain, (![B_239, D_240, A_241, C_242]: (k1_xboole_0=B_239 | v1_funct_2(D_240, A_241, C_242) | ~r1_tarski(k2_relset_1(A_241, B_239, D_240), C_242) | ~m1_subset_1(D_240, k1_zfmisc_1(k2_zfmisc_1(A_241, B_239))) | ~v1_funct_2(D_240, A_241, B_239) | ~v1_funct_1(D_240))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.43/2.77  tff(c_1422, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', k1_relat_1('#skF_6')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_584, c_1420])).
% 8.43/2.77  tff(c_1425, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1422])).
% 8.43/2.77  tff(c_1426, plain, (v1_funct_2('#skF_5', '#skF_3', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1425])).
% 8.43/2.77  tff(c_1529, plain, (![B_257, D_258, A_259, C_260]: (k1_xboole_0=B_257 | m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_259, C_260))) | ~r1_tarski(k2_relset_1(A_259, B_257, D_258), C_260) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_259, B_257))) | ~v1_funct_2(D_258, A_259, B_257) | ~v1_funct_1(D_258))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.43/2.77  tff(c_1531, plain, (k1_xboole_0='#skF_4' | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_584, c_1529])).
% 8.43/2.77  tff(c_1534, plain, (k1_xboole_0='#skF_4' | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_1531])).
% 8.43/2.77  tff(c_1535, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6'))))), inference(splitLeft, [status(thm)], [c_1534])).
% 8.43/2.77  tff(c_14, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.43/2.77  tff(c_1290, plain, (![D_224, C_225, B_226, A_227]: (r2_hidden(k1_funct_1(D_224, C_225), B_226) | k1_xboole_0=B_226 | ~r2_hidden(C_225, A_227) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))) | ~v1_funct_2(D_224, A_227, B_226) | ~v1_funct_1(D_224))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.43/2.77  tff(c_2837, plain, (![D_344, A_345, B_346, B_347]: (r2_hidden(k1_funct_1(D_344, A_345), B_346) | k1_xboole_0=B_346 | ~m1_subset_1(D_344, k1_zfmisc_1(k2_zfmisc_1(B_347, B_346))) | ~v1_funct_2(D_344, B_347, B_346) | ~v1_funct_1(D_344) | v1_xboole_0(B_347) | ~m1_subset_1(A_345, B_347))), inference(resolution, [status(thm)], [c_14, c_1290])).
% 8.43/2.77  tff(c_2842, plain, (![A_345]: (r2_hidden(k1_funct_1('#skF_5', A_345), k1_relat_1('#skF_6')) | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_5', '#skF_3', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_345, '#skF_3'))), inference(resolution, [status(thm)], [c_1535, c_2837])).
% 8.43/2.77  tff(c_2863, plain, (![A_345]: (r2_hidden(k1_funct_1('#skF_5', A_345), k1_relat_1('#skF_6')) | k1_relat_1('#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_3') | ~m1_subset_1(A_345, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1426, c_2842])).
% 8.43/2.77  tff(c_2864, plain, (![A_345]: (r2_hidden(k1_funct_1('#skF_5', A_345), k1_relat_1('#skF_6')) | k1_relat_1('#skF_6')=k1_xboole_0 | ~m1_subset_1(A_345, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_864, c_2863])).
% 8.43/2.77  tff(c_3295, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2864])).
% 8.43/2.77  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.43/2.77  tff(c_1575, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_1535, c_16])).
% 8.43/2.77  tff(c_466, plain, (![B_134, A_1]: (~v1_xboole_0(B_134) | ~r1_tarski(A_1, B_134) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_460])).
% 8.43/2.77  tff(c_1604, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6'))) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1575, c_466])).
% 8.43/2.77  tff(c_1618, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_1604])).
% 8.43/2.77  tff(c_3301, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3295, c_1618])).
% 8.43/2.77  tff(c_3315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_3301])).
% 8.43/2.77  tff(c_3318, plain, (![A_360]: (r2_hidden(k1_funct_1('#skF_5', A_360), k1_relat_1('#skF_6')) | ~m1_subset_1(A_360, '#skF_3'))), inference(splitRight, [status(thm)], [c_2864])).
% 8.43/2.77  tff(c_50, plain, (![A_32, B_33, C_35]: (k7_partfun1(A_32, B_33, C_35)=k1_funct_1(B_33, C_35) | ~r2_hidden(C_35, k1_relat_1(B_33)) | ~v1_funct_1(B_33) | ~v5_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.43/2.77  tff(c_3322, plain, (![A_32, A_360]: (k7_partfun1(A_32, '#skF_6', k1_funct_1('#skF_5', A_360))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_360)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_32) | ~v1_relat_1('#skF_6') | ~m1_subset_1(A_360, '#skF_3'))), inference(resolution, [status(thm)], [c_3318, c_50])).
% 8.43/2.77  tff(c_6082, plain, (![A_546, A_547]: (k7_partfun1(A_546, '#skF_6', k1_funct_1('#skF_5', A_547))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', A_547)) | ~v5_relat_1('#skF_6', A_546) | ~m1_subset_1(A_547, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_78, c_3322])).
% 8.43/2.77  tff(c_68, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.43/2.77  tff(c_6092, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6082, c_68])).
% 8.43/2.77  tff(c_6102, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_211, c_6092])).
% 8.43/2.77  tff(c_6107, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1670, c_6102])).
% 8.43/2.77  tff(c_6111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_6107])).
% 8.43/2.77  tff(c_6112, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1604])).
% 8.43/2.77  tff(c_6177, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6112, c_70])).
% 8.43/2.77  tff(c_582, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_553])).
% 8.43/2.77  tff(c_952, plain, (![B_195, A_196, C_197]: (k1_xboole_0=B_195 | k1_relset_1(A_196, B_195, C_197)=A_196 | ~v1_funct_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.43/2.77  tff(c_970, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_952])).
% 8.43/2.77  tff(c_985, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_582, c_970])).
% 8.43/2.77  tff(c_987, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_985])).
% 8.43/2.77  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.43/2.77  tff(c_187, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_166])).
% 8.43/2.77  tff(c_391, plain, (![A_119]: (v4_relat_1(k1_xboole_0, A_119))), inference(resolution, [status(thm)], [c_12, c_368])).
% 8.43/2.77  tff(c_319, plain, (![B_114, A_115]: (r1_tarski(k1_relat_1(B_114), A_115) | ~v4_relat_1(B_114, A_115) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.43/2.77  tff(c_119, plain, (![B_77, A_78]: (~r1_tarski(B_77, A_78) | ~r2_hidden(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.43/2.77  tff(c_123, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_119])).
% 8.43/2.77  tff(c_682, plain, (![B_166]: (k1_relat_1(B_166)=k1_xboole_0 | ~v4_relat_1(B_166, '#skF_1'(k1_relat_1(B_166))) | ~v1_relat_1(B_166))), inference(resolution, [status(thm)], [c_319, c_123])).
% 8.43/2.77  tff(c_690, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_391, c_682])).
% 8.43/2.77  tff(c_694, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_187, c_690])).
% 8.43/2.77  tff(c_6147, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6112, c_6112, c_694])).
% 8.43/2.77  tff(c_6178, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_987, c_6147])).
% 8.43/2.77  tff(c_6185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6177, c_6178])).
% 8.43/2.77  tff(c_6186, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1534])).
% 8.43/2.77  tff(c_6250, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6186, c_2])).
% 8.43/2.77  tff(c_6253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_6250])).
% 8.43/2.77  tff(c_6254, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1425])).
% 8.43/2.77  tff(c_6313, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6254, c_2])).
% 8.43/2.77  tff(c_6316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_6313])).
% 8.43/2.77  tff(c_6317, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_985])).
% 8.43/2.77  tff(c_6360, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_2])).
% 8.43/2.77  tff(c_6363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_6360])).
% 8.43/2.77  tff(c_6364, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_857])).
% 8.43/2.77  tff(c_6381, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6364, c_582])).
% 8.43/2.77  tff(c_6581, plain, (![B_569, A_570, C_571]: (k1_xboole_0=B_569 | k1_relset_1(A_570, B_569, C_571)=A_570 | ~v1_funct_2(C_571, A_570, B_569) | ~m1_subset_1(C_571, k1_zfmisc_1(k2_zfmisc_1(A_570, B_569))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.43/2.77  tff(c_6599, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_6581])).
% 8.43/2.77  tff(c_6615, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6381, c_6599])).
% 8.43/2.77  tff(c_6616, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_70, c_6615])).
% 8.43/2.77  tff(c_6664, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6616, c_2])).
% 8.43/2.77  tff(c_6667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_6664])).
% 8.43/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.43/2.77  
% 8.43/2.77  Inference rules
% 8.43/2.77  ----------------------
% 8.43/2.77  #Ref     : 0
% 8.43/2.77  #Sup     : 1311
% 8.43/2.77  #Fact    : 0
% 8.43/2.77  #Define  : 0
% 8.43/2.77  #Split   : 46
% 8.43/2.77  #Chain   : 0
% 8.43/2.77  #Close   : 0
% 8.43/2.77  
% 8.43/2.77  Ordering : KBO
% 8.43/2.77  
% 8.43/2.77  Simplification rules
% 8.43/2.77  ----------------------
% 8.43/2.77  #Subsume      : 370
% 8.43/2.77  #Demod        : 1350
% 8.43/2.77  #Tautology    : 354
% 8.43/2.77  #SimpNegUnit  : 119
% 8.43/2.77  #BackRed      : 429
% 8.43/2.77  
% 8.43/2.77  #Partial instantiations: 0
% 8.43/2.77  #Strategies tried      : 1
% 8.43/2.77  
% 8.43/2.77  Timing (in seconds)
% 8.43/2.77  ----------------------
% 8.43/2.77  Preprocessing        : 0.37
% 8.43/2.77  Parsing              : 0.20
% 8.43/2.77  CNF conversion       : 0.03
% 8.43/2.77  Main loop            : 1.62
% 8.43/2.77  Inferencing          : 0.46
% 8.43/2.77  Reduction            : 0.53
% 8.43/2.77  Demodulation         : 0.36
% 8.43/2.77  BG Simplification    : 0.06
% 8.43/2.77  Subsumption          : 0.45
% 8.43/2.77  Abstraction          : 0.07
% 8.43/2.77  MUC search           : 0.00
% 8.43/2.77  Cooper               : 0.00
% 8.43/2.77  Total                : 2.04
% 8.43/2.77  Index Insertion      : 0.00
% 8.43/2.77  Index Deletion       : 0.00
% 8.43/2.77  Index Matching       : 0.00
% 8.43/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
