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
% DateTime   : Thu Dec  3 10:17:47 EST 2020

% Result     : Theorem 9.48s
% Output     : CNFRefutation 9.63s
% Verified   : 
% Statistics : Number of formulae       :  188 (1195 expanded)
%              Number of leaves         :   54 ( 426 expanded)
%              Depth                    :   19
%              Number of atoms          :  405 (3982 expanded)
%              Number of equality atoms :   98 ( 956 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_218,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_162,axiom,(
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

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_127,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_193,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_174,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_110,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    m1_subset_1('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_108,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_106,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_104,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_100,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_348,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_361,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_100,c_348])).

tff(c_96,plain,(
    r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),k1_relset_1('#skF_8','#skF_6','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_367,plain,(
    r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_96])).

tff(c_102,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_4456,plain,(
    ! [B_552,C_551,E_553,D_549,F_548,A_550] :
      ( k1_funct_1(k8_funct_2(B_552,C_551,A_550,D_549,E_553),F_548) = k1_funct_1(E_553,k1_funct_1(D_549,F_548))
      | k1_xboole_0 = B_552
      | ~ r1_tarski(k2_relset_1(B_552,C_551,D_549),k1_relset_1(C_551,A_550,E_553))
      | ~ m1_subset_1(F_548,B_552)
      | ~ m1_subset_1(E_553,k1_zfmisc_1(k2_zfmisc_1(C_551,A_550)))
      | ~ v1_funct_1(E_553)
      | ~ m1_subset_1(D_549,k1_zfmisc_1(k2_zfmisc_1(B_552,C_551)))
      | ~ v1_funct_2(D_549,B_552,C_551)
      | ~ v1_funct_1(D_549)
      | v1_xboole_0(C_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4464,plain,(
    ! [B_552,D_549,F_548] :
      ( k1_funct_1(k8_funct_2(B_552,'#skF_8','#skF_6',D_549,'#skF_10'),F_548) = k1_funct_1('#skF_10',k1_funct_1(D_549,F_548))
      | k1_xboole_0 = B_552
      | ~ r1_tarski(k2_relset_1(B_552,'#skF_8',D_549),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(F_548,B_552)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6')))
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(D_549,k1_zfmisc_1(k2_zfmisc_1(B_552,'#skF_8')))
      | ~ v1_funct_2(D_549,B_552,'#skF_8')
      | ~ v1_funct_1(D_549)
      | v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_4456])).

tff(c_4474,plain,(
    ! [B_552,D_549,F_548] :
      ( k1_funct_1(k8_funct_2(B_552,'#skF_8','#skF_6',D_549,'#skF_10'),F_548) = k1_funct_1('#skF_10',k1_funct_1(D_549,F_548))
      | k1_xboole_0 = B_552
      | ~ r1_tarski(k2_relset_1(B_552,'#skF_8',D_549),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(F_548,B_552)
      | ~ m1_subset_1(D_549,k1_zfmisc_1(k2_zfmisc_1(B_552,'#skF_8')))
      | ~ v1_funct_2(D_549,B_552,'#skF_8')
      | ~ v1_funct_1(D_549)
      | v1_xboole_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_4464])).

tff(c_4501,plain,(
    ! [B_563,D_564,F_565] :
      ( k1_funct_1(k8_funct_2(B_563,'#skF_8','#skF_6',D_564,'#skF_10'),F_565) = k1_funct_1('#skF_10',k1_funct_1(D_564,F_565))
      | k1_xboole_0 = B_563
      | ~ r1_tarski(k2_relset_1(B_563,'#skF_8',D_564),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(F_565,B_563)
      | ~ m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(B_563,'#skF_8')))
      | ~ v1_funct_2(D_564,B_563,'#skF_8')
      | ~ v1_funct_1(D_564) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_4474])).

tff(c_4503,plain,(
    ! [F_565] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_565) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_565))
      | k1_xboole_0 = '#skF_7'
      | ~ m1_subset_1(F_565,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_367,c_4501])).

tff(c_4506,plain,(
    ! [F_565] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_565) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_565))
      | k1_xboole_0 = '#skF_7'
      | ~ m1_subset_1(F_565,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_4503])).

tff(c_4507,plain,(
    ! [F_565] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_565) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_565))
      | ~ m1_subset_1(F_565,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4506])).

tff(c_276,plain,(
    ! [C_150,B_151,A_152] :
      ( v5_relat_1(C_150,B_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_289,plain,(
    v5_relat_1('#skF_10','#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_276])).

tff(c_155,plain,(
    ! [C_128,A_129,B_130] :
      ( v1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_168,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_100,c_155])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_167,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_104,c_155])).

tff(c_360,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_104,c_348])).

tff(c_619,plain,(
    ! [B_200,A_201,C_202] :
      ( k1_xboole_0 = B_200
      | k1_relset_1(A_201,B_200,C_202) = A_201
      | ~ v1_funct_2(C_202,A_201,B_200)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_626,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_104,c_619])).

tff(c_633,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_360,c_626])).

tff(c_636,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_633])).

tff(c_1005,plain,(
    ! [A_239,B_240,D_241] :
      ( r2_hidden('#skF_5'(A_239,B_240,k9_relat_1(A_239,B_240),D_241),k1_relat_1(A_239))
      | ~ r2_hidden(D_241,k9_relat_1(A_239,B_240))
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1030,plain,(
    ! [B_240,D_241] :
      ( r2_hidden('#skF_5'('#skF_9',B_240,k9_relat_1('#skF_9',B_240),D_241),'#skF_7')
      | ~ r2_hidden(D_241,k9_relat_1('#skF_9',B_240))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_1005])).

tff(c_1095,plain,(
    ! [B_246,D_247] :
      ( r2_hidden('#skF_5'('#skF_9',B_246,k9_relat_1('#skF_9',B_246),D_247),'#skF_7')
      | ~ r2_hidden(D_247,k9_relat_1('#skF_9',B_246)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_108,c_1030])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1112,plain,(
    ! [D_247,B_246] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_247,k9_relat_1('#skF_9',B_246)) ) ),
    inference(resolution,[status(thm)],[c_1095,c_2])).

tff(c_1177,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_3044,plain,(
    ! [B_414,D_415,A_416,C_417] :
      ( k1_xboole_0 = B_414
      | v1_funct_2(D_415,A_416,C_417)
      | ~ r1_tarski(k2_relset_1(A_416,B_414,D_415),C_417)
      | ~ m1_subset_1(D_415,k1_zfmisc_1(k2_zfmisc_1(A_416,B_414)))
      | ~ v1_funct_2(D_415,A_416,B_414)
      | ~ v1_funct_1(D_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_3046,plain,
    ( k1_xboole_0 = '#skF_8'
    | v1_funct_2('#skF_9','#skF_7',k1_relat_1('#skF_10'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_367,c_3044])).

tff(c_3049,plain,
    ( k1_xboole_0 = '#skF_8'
    | v1_funct_2('#skF_9','#skF_7',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_3046])).

tff(c_3050,plain,(
    v1_funct_2('#skF_9','#skF_7',k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_3049])).

tff(c_3363,plain,(
    ! [B_450,D_451,A_452,C_453] :
      ( k1_xboole_0 = B_450
      | m1_subset_1(D_451,k1_zfmisc_1(k2_zfmisc_1(A_452,C_453)))
      | ~ r1_tarski(k2_relset_1(A_452,B_450,D_451),C_453)
      | ~ m1_subset_1(D_451,k1_zfmisc_1(k2_zfmisc_1(A_452,B_450)))
      | ~ v1_funct_2(D_451,A_452,B_450)
      | ~ v1_funct_1(D_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_3365,plain,
    ( k1_xboole_0 = '#skF_8'
    | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_relat_1('#skF_10'))))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_367,c_3363])).

tff(c_3368,plain,
    ( k1_xboole_0 = '#skF_8'
    | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_relat_1('#skF_10')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_3365])).

tff(c_3369,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_relat_1('#skF_10')))) ),
    inference(splitLeft,[status(thm)],[c_3368])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2464,plain,(
    ! [D_359,C_360,B_361,A_362] :
      ( r2_hidden(k1_funct_1(D_359,C_360),B_361)
      | k1_xboole_0 = B_361
      | ~ r2_hidden(C_360,A_362)
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361)))
      | ~ v1_funct_2(D_359,A_362,B_361)
      | ~ v1_funct_1(D_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_6869,plain,(
    ! [D_833,A_834,B_835,B_836] :
      ( r2_hidden(k1_funct_1(D_833,A_834),B_835)
      | k1_xboole_0 = B_835
      | ~ m1_subset_1(D_833,k1_zfmisc_1(k2_zfmisc_1(B_836,B_835)))
      | ~ v1_funct_2(D_833,B_836,B_835)
      | ~ v1_funct_1(D_833)
      | v1_xboole_0(B_836)
      | ~ m1_subset_1(A_834,B_836) ) ),
    inference(resolution,[status(thm)],[c_12,c_2464])).

tff(c_6871,plain,(
    ! [A_834] :
      ( r2_hidden(k1_funct_1('#skF_9',A_834),k1_relat_1('#skF_10'))
      | k1_relat_1('#skF_10') = k1_xboole_0
      | ~ v1_funct_2('#skF_9','#skF_7',k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_9')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_834,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3369,c_6869])).

tff(c_6881,plain,(
    ! [A_834] :
      ( r2_hidden(k1_funct_1('#skF_9',A_834),k1_relat_1('#skF_10'))
      | k1_relat_1('#skF_10') = k1_xboole_0
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_834,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_3050,c_6871])).

tff(c_6882,plain,(
    ! [A_834] :
      ( r2_hidden(k1_funct_1('#skF_9',A_834),k1_relat_1('#skF_10'))
      | k1_relat_1('#skF_10') = k1_xboole_0
      | ~ m1_subset_1(A_834,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1177,c_6881])).

tff(c_7093,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6882])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_214,plain,(
    ! [C_138,B_139,A_140] :
      ( ~ v1_xboole_0(C_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(C_138))
      | ~ r2_hidden(A_140,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ! [B_143,A_144,A_145] :
      ( ~ v1_xboole_0(B_143)
      | ~ r2_hidden(A_144,A_145)
      | ~ r1_tarski(A_145,B_143) ) ),
    inference(resolution,[status(thm)],[c_16,c_214])).

tff(c_235,plain,(
    ! [B_146,A_147] :
      ( ~ v1_xboole_0(B_146)
      | ~ r1_tarski(A_147,B_146)
      | v1_xboole_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_249,plain,
    ( ~ v1_xboole_0(k1_relset_1('#skF_8','#skF_6','#skF_10'))
    | v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_96,c_235])).

tff(c_380,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_10'))
    | v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_249])).

tff(c_381,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_7106,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7093,c_381])).

tff(c_7111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7106])).

tff(c_7115,plain,(
    ! [A_846] :
      ( r2_hidden(k1_funct_1('#skF_9',A_846),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(A_846,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_6882])).

tff(c_74,plain,(
    ! [A_75,B_76,C_78] :
      ( k7_partfun1(A_75,B_76,C_78) = k1_funct_1(B_76,C_78)
      | ~ r2_hidden(C_78,k1_relat_1(B_76))
      | ~ v1_funct_1(B_76)
      | ~ v5_relat_1(B_76,A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_7121,plain,(
    ! [A_75,A_846] :
      ( k7_partfun1(A_75,'#skF_10',k1_funct_1('#skF_9',A_846)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',A_846))
      | ~ v1_funct_1('#skF_10')
      | ~ v5_relat_1('#skF_10',A_75)
      | ~ v1_relat_1('#skF_10')
      | ~ m1_subset_1(A_846,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7115,c_74])).

tff(c_7779,plain,(
    ! [A_884,A_885] :
      ( k7_partfun1(A_884,'#skF_10',k1_funct_1('#skF_9',A_885)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',A_885))
      | ~ v5_relat_1('#skF_10',A_884)
      | ~ m1_subset_1(A_885,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_102,c_7121])).

tff(c_92,plain,(
    k7_partfun1('#skF_6','#skF_10',k1_funct_1('#skF_9','#skF_11')) != k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_7785,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ v5_relat_1('#skF_10','#skF_6')
    | ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7779,c_92])).

tff(c_7805,plain,(
    k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_289,c_7785])).

tff(c_7815,plain,(
    ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4507,c_7805])).

tff(c_7819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_7815])).

tff(c_7820,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3368])).

tff(c_7886,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7820,c_6])).

tff(c_7889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_7886])).

tff(c_7890,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3049])).

tff(c_7946,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7890,c_6])).

tff(c_7949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_7946])).

tff(c_7951,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7959,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7951,c_8])).

tff(c_7965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_7959])).

tff(c_7967,plain,(
    v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_7975,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7967,c_8])).

tff(c_7986,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7975,c_361])).

tff(c_8194,plain,(
    ! [B_905,C_906,A_907] :
      ( k1_xboole_0 = B_905
      | v1_funct_2(C_906,A_907,B_905)
      | k1_relset_1(A_907,B_905,C_906) != A_907
      | ~ m1_subset_1(C_906,k1_zfmisc_1(k2_zfmisc_1(A_907,B_905))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8204,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2('#skF_10','#skF_8','#skF_6')
    | k1_relset_1('#skF_8','#skF_6','#skF_10') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_100,c_8194])).

tff(c_8209,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2('#skF_10','#skF_8','#skF_6')
    | k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7986,c_8204])).

tff(c_8210,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_8209])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7966,plain,(
    v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_8000,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7966,c_8])).

tff(c_10906,plain,(
    ! [B_1134,D_1135,A_1136,C_1137] :
      ( k1_xboole_0 = B_1134
      | v1_funct_2(D_1135,A_1136,C_1137)
      | ~ r1_tarski(k2_relset_1(A_1136,B_1134,D_1135),C_1137)
      | ~ m1_subset_1(D_1135,k1_zfmisc_1(k2_zfmisc_1(A_1136,B_1134)))
      | ~ v1_funct_2(D_1135,A_1136,B_1134)
      | ~ v1_funct_1(D_1135) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_10908,plain,(
    ! [C_1137] :
      ( k1_xboole_0 = '#skF_8'
      | v1_funct_2('#skF_9','#skF_7',C_1137)
      | ~ r1_tarski(k1_xboole_0,C_1137)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8000,c_10906])).

tff(c_10910,plain,(
    ! [C_1137] :
      ( k1_xboole_0 = '#skF_8'
      | v1_funct_2('#skF_9','#skF_7',C_1137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_10,c_10908])).

tff(c_10911,plain,(
    ! [C_1137] : v1_funct_2('#skF_9','#skF_7',C_1137) ),
    inference(negUnitSimplification,[status(thm)],[c_8210,c_10910])).

tff(c_11110,plain,(
    ! [B_1161,D_1162,A_1163,C_1164] :
      ( k1_xboole_0 = B_1161
      | m1_subset_1(D_1162,k1_zfmisc_1(k2_zfmisc_1(A_1163,C_1164)))
      | ~ r1_tarski(k2_relset_1(A_1163,B_1161,D_1162),C_1164)
      | ~ m1_subset_1(D_1162,k1_zfmisc_1(k2_zfmisc_1(A_1163,B_1161)))
      | ~ v1_funct_2(D_1162,A_1163,B_1161)
      | ~ v1_funct_1(D_1162) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_11112,plain,(
    ! [C_1164] :
      ( k1_xboole_0 = '#skF_8'
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',C_1164)))
      | ~ r1_tarski(k1_xboole_0,C_1164)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8000,c_11110])).

tff(c_11114,plain,(
    ! [C_1164] :
      ( k1_xboole_0 = '#skF_8'
      | m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',C_1164))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_10911,c_104,c_10,c_11112])).

tff(c_11117,plain,(
    ! [C_1165] : m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',C_1165))) ),
    inference(negUnitSimplification,[status(thm)],[c_8210,c_11114])).

tff(c_64,plain,(
    ! [C_74,A_72] :
      ( k1_xboole_0 = C_74
      | ~ v1_funct_2(C_74,A_72,k1_xboole_0)
      | k1_xboole_0 = A_72
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_11127,plain,
    ( k1_xboole_0 = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_7',k1_xboole_0)
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_11117,c_64])).

tff(c_11152,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10911,c_11127])).

tff(c_11153,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_11152])).

tff(c_11230,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11153,c_6])).

tff(c_178,plain,(
    ! [A_133,A_134,B_135] :
      ( v1_relat_1(A_133)
      | ~ r1_tarski(A_133,k2_zfmisc_1(A_134,B_135)) ) ),
    inference(resolution,[status(thm)],[c_16,c_155])).

tff(c_193,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_178])).

tff(c_326,plain,(
    ! [A_160,B_161,A_162] :
      ( v5_relat_1(A_160,B_161)
      | ~ r1_tarski(A_160,k2_zfmisc_1(A_162,B_161)) ) ),
    inference(resolution,[status(thm)],[c_16,c_276])).

tff(c_346,plain,(
    ! [B_161] : v5_relat_1(k1_xboole_0,B_161) ),
    inference(resolution,[status(thm)],[c_10,c_326])).

tff(c_253,plain,(
    ! [B_148,A_149] :
      ( r1_tarski(k2_relat_1(B_148),A_149)
      | ~ v5_relat_1(B_148,A_149)
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_125,plain,(
    ! [A_122] :
      ( v1_xboole_0(A_122)
      | r2_hidden('#skF_1'(A_122),A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [B_62,A_61] :
      ( ~ r1_tarski(B_62,A_61)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_132,plain,(
    ! [A_122] :
      ( ~ r1_tarski(A_122,'#skF_1'(A_122))
      | v1_xboole_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_125,c_52])).

tff(c_8051,plain,(
    ! [B_893] :
      ( v1_xboole_0(k2_relat_1(B_893))
      | ~ v5_relat_1(B_893,'#skF_1'(k2_relat_1(B_893)))
      | ~ v1_relat_1(B_893) ) ),
    inference(resolution,[status(thm)],[c_253,c_132])).

tff(c_8055,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_346,c_8051])).

tff(c_8058,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_8055])).

tff(c_8066,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8058,c_8])).

tff(c_11218,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11153,c_11153,c_8066])).

tff(c_8261,plain,(
    ! [B_915,A_916,C_917] :
      ( k1_xboole_0 = B_915
      | k1_relset_1(A_916,B_915,C_917) = A_916
      | ~ v1_funct_2(C_917,A_916,B_915)
      | ~ m1_subset_1(C_917,k1_zfmisc_1(k2_zfmisc_1(A_916,B_915))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8268,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_104,c_8261])).

tff(c_8275,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_360,c_8268])).

tff(c_8276,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_8210,c_8275])).

tff(c_8030,plain,(
    ! [B_888,A_889] :
      ( r2_hidden(k1_funct_1(B_888,A_889),k2_relat_1(B_888))
      | ~ r2_hidden(A_889,k1_relat_1(B_888))
      | ~ v1_funct_1(B_888)
      | ~ v1_relat_1(B_888) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8041,plain,(
    ! [B_888,A_889] :
      ( ~ v1_xboole_0(k2_relat_1(B_888))
      | ~ r2_hidden(A_889,k1_relat_1(B_888))
      | ~ v1_funct_1(B_888)
      | ~ v1_relat_1(B_888) ) ),
    inference(resolution,[status(thm)],[c_8030,c_2])).

tff(c_8284,plain,(
    ! [A_889] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_9'))
      | ~ r2_hidden(A_889,'#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8276,c_8041])).

tff(c_8288,plain,(
    ! [A_889] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_9'))
      | ~ r2_hidden(A_889,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_108,c_8284])).

tff(c_8294,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_8288])).

tff(c_11249,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11218,c_8294])).

tff(c_11252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11230,c_11249])).

tff(c_11255,plain,(
    ! [A_1166] : ~ r2_hidden(A_1166,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_8288])).

tff(c_11265,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_11255])).

tff(c_11271,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_11265,c_8])).

tff(c_11276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_11271])).

tff(c_11278,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8209])).

tff(c_11297,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_6])).

tff(c_11300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_11297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.48/3.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/3.45  
% 9.63/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/3.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 9.63/3.46  
% 9.63/3.46  %Foreground sorts:
% 9.63/3.46  
% 9.63/3.46  
% 9.63/3.46  %Background operators:
% 9.63/3.46  
% 9.63/3.46  
% 9.63/3.46  %Foreground operators:
% 9.63/3.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.63/3.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.63/3.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.63/3.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.63/3.46  tff('#skF_11', type, '#skF_11': $i).
% 9.63/3.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.63/3.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.63/3.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.63/3.46  tff('#skF_7', type, '#skF_7': $i).
% 9.63/3.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.63/3.46  tff('#skF_10', type, '#skF_10': $i).
% 9.63/3.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.63/3.46  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 9.63/3.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.63/3.46  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 9.63/3.46  tff('#skF_6', type, '#skF_6': $i).
% 9.63/3.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.63/3.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.63/3.46  tff('#skF_9', type, '#skF_9': $i).
% 9.63/3.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.63/3.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.63/3.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.63/3.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.63/3.46  tff('#skF_8', type, '#skF_8': $i).
% 9.63/3.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.63/3.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 9.63/3.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.63/3.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.63/3.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.63/3.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.63/3.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.63/3.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.63/3.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.63/3.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.63/3.46  
% 9.63/3.48  tff(f_218, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 9.63/3.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.63/3.48  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.63/3.48  tff(f_162, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 9.63/3.48  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.63/3.48  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.63/3.48  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.63/3.48  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.63/3.48  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 9.63/3.48  tff(f_193, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 9.63/3.48  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.63/3.48  tff(f_174, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 9.63/3.48  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.63/3.48  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.63/3.48  tff(f_138, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 9.63/3.48  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.63/3.48  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.63/3.48  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.63/3.48  tff(f_95, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.63/3.48  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 9.63/3.48  tff(c_110, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_94, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.63/3.48  tff(c_98, plain, (m1_subset_1('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_108, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_106, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_104, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_100, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_348, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.63/3.48  tff(c_361, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_100, c_348])).
% 9.63/3.48  tff(c_96, plain, (r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), k1_relset_1('#skF_8', '#skF_6', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_367, plain, (r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_96])).
% 9.63/3.48  tff(c_102, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_4456, plain, (![B_552, C_551, E_553, D_549, F_548, A_550]: (k1_funct_1(k8_funct_2(B_552, C_551, A_550, D_549, E_553), F_548)=k1_funct_1(E_553, k1_funct_1(D_549, F_548)) | k1_xboole_0=B_552 | ~r1_tarski(k2_relset_1(B_552, C_551, D_549), k1_relset_1(C_551, A_550, E_553)) | ~m1_subset_1(F_548, B_552) | ~m1_subset_1(E_553, k1_zfmisc_1(k2_zfmisc_1(C_551, A_550))) | ~v1_funct_1(E_553) | ~m1_subset_1(D_549, k1_zfmisc_1(k2_zfmisc_1(B_552, C_551))) | ~v1_funct_2(D_549, B_552, C_551) | ~v1_funct_1(D_549) | v1_xboole_0(C_551))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.63/3.48  tff(c_4464, plain, (![B_552, D_549, F_548]: (k1_funct_1(k8_funct_2(B_552, '#skF_8', '#skF_6', D_549, '#skF_10'), F_548)=k1_funct_1('#skF_10', k1_funct_1(D_549, F_548)) | k1_xboole_0=B_552 | ~r1_tarski(k2_relset_1(B_552, '#skF_8', D_549), k1_relat_1('#skF_10')) | ~m1_subset_1(F_548, B_552) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6'))) | ~v1_funct_1('#skF_10') | ~m1_subset_1(D_549, k1_zfmisc_1(k2_zfmisc_1(B_552, '#skF_8'))) | ~v1_funct_2(D_549, B_552, '#skF_8') | ~v1_funct_1(D_549) | v1_xboole_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_361, c_4456])).
% 9.63/3.48  tff(c_4474, plain, (![B_552, D_549, F_548]: (k1_funct_1(k8_funct_2(B_552, '#skF_8', '#skF_6', D_549, '#skF_10'), F_548)=k1_funct_1('#skF_10', k1_funct_1(D_549, F_548)) | k1_xboole_0=B_552 | ~r1_tarski(k2_relset_1(B_552, '#skF_8', D_549), k1_relat_1('#skF_10')) | ~m1_subset_1(F_548, B_552) | ~m1_subset_1(D_549, k1_zfmisc_1(k2_zfmisc_1(B_552, '#skF_8'))) | ~v1_funct_2(D_549, B_552, '#skF_8') | ~v1_funct_1(D_549) | v1_xboole_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_4464])).
% 9.63/3.48  tff(c_4501, plain, (![B_563, D_564, F_565]: (k1_funct_1(k8_funct_2(B_563, '#skF_8', '#skF_6', D_564, '#skF_10'), F_565)=k1_funct_1('#skF_10', k1_funct_1(D_564, F_565)) | k1_xboole_0=B_563 | ~r1_tarski(k2_relset_1(B_563, '#skF_8', D_564), k1_relat_1('#skF_10')) | ~m1_subset_1(F_565, B_563) | ~m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(B_563, '#skF_8'))) | ~v1_funct_2(D_564, B_563, '#skF_8') | ~v1_funct_1(D_564))), inference(negUnitSimplification, [status(thm)], [c_110, c_4474])).
% 9.63/3.48  tff(c_4503, plain, (![F_565]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_565)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_565)) | k1_xboole_0='#skF_7' | ~m1_subset_1(F_565, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9'))), inference(resolution, [status(thm)], [c_367, c_4501])).
% 9.63/3.48  tff(c_4506, plain, (![F_565]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_565)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_565)) | k1_xboole_0='#skF_7' | ~m1_subset_1(F_565, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_4503])).
% 9.63/3.48  tff(c_4507, plain, (![F_565]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_565)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_565)) | ~m1_subset_1(F_565, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_4506])).
% 9.63/3.48  tff(c_276, plain, (![C_150, B_151, A_152]: (v5_relat_1(C_150, B_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.63/3.48  tff(c_289, plain, (v5_relat_1('#skF_10', '#skF_6')), inference(resolution, [status(thm)], [c_100, c_276])).
% 9.63/3.48  tff(c_155, plain, (![C_128, A_129, B_130]: (v1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.63/3.48  tff(c_168, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_100, c_155])).
% 9.63/3.48  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.63/3.48  tff(c_167, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_104, c_155])).
% 9.63/3.48  tff(c_360, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_104, c_348])).
% 9.63/3.48  tff(c_619, plain, (![B_200, A_201, C_202]: (k1_xboole_0=B_200 | k1_relset_1(A_201, B_200, C_202)=A_201 | ~v1_funct_2(C_202, A_201, B_200) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.63/3.48  tff(c_626, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_104, c_619])).
% 9.63/3.48  tff(c_633, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_360, c_626])).
% 9.63/3.48  tff(c_636, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_633])).
% 9.63/3.48  tff(c_1005, plain, (![A_239, B_240, D_241]: (r2_hidden('#skF_5'(A_239, B_240, k9_relat_1(A_239, B_240), D_241), k1_relat_1(A_239)) | ~r2_hidden(D_241, k9_relat_1(A_239, B_240)) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.63/3.48  tff(c_1030, plain, (![B_240, D_241]: (r2_hidden('#skF_5'('#skF_9', B_240, k9_relat_1('#skF_9', B_240), D_241), '#skF_7') | ~r2_hidden(D_241, k9_relat_1('#skF_9', B_240)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_636, c_1005])).
% 9.63/3.48  tff(c_1095, plain, (![B_246, D_247]: (r2_hidden('#skF_5'('#skF_9', B_246, k9_relat_1('#skF_9', B_246), D_247), '#skF_7') | ~r2_hidden(D_247, k9_relat_1('#skF_9', B_246)))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_108, c_1030])).
% 9.63/3.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.63/3.48  tff(c_1112, plain, (![D_247, B_246]: (~v1_xboole_0('#skF_7') | ~r2_hidden(D_247, k9_relat_1('#skF_9', B_246)))), inference(resolution, [status(thm)], [c_1095, c_2])).
% 9.63/3.48  tff(c_1177, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1112])).
% 9.63/3.48  tff(c_3044, plain, (![B_414, D_415, A_416, C_417]: (k1_xboole_0=B_414 | v1_funct_2(D_415, A_416, C_417) | ~r1_tarski(k2_relset_1(A_416, B_414, D_415), C_417) | ~m1_subset_1(D_415, k1_zfmisc_1(k2_zfmisc_1(A_416, B_414))) | ~v1_funct_2(D_415, A_416, B_414) | ~v1_funct_1(D_415))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.63/3.48  tff(c_3046, plain, (k1_xboole_0='#skF_8' | v1_funct_2('#skF_9', '#skF_7', k1_relat_1('#skF_10')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_367, c_3044])).
% 9.63/3.48  tff(c_3049, plain, (k1_xboole_0='#skF_8' | v1_funct_2('#skF_9', '#skF_7', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_3046])).
% 9.63/3.48  tff(c_3050, plain, (v1_funct_2('#skF_9', '#skF_7', k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_3049])).
% 9.63/3.48  tff(c_3363, plain, (![B_450, D_451, A_452, C_453]: (k1_xboole_0=B_450 | m1_subset_1(D_451, k1_zfmisc_1(k2_zfmisc_1(A_452, C_453))) | ~r1_tarski(k2_relset_1(A_452, B_450, D_451), C_453) | ~m1_subset_1(D_451, k1_zfmisc_1(k2_zfmisc_1(A_452, B_450))) | ~v1_funct_2(D_451, A_452, B_450) | ~v1_funct_1(D_451))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.63/3.48  tff(c_3365, plain, (k1_xboole_0='#skF_8' | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_relat_1('#skF_10')))) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_367, c_3363])).
% 9.63/3.48  tff(c_3368, plain, (k1_xboole_0='#skF_8' | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_relat_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_3365])).
% 9.63/3.48  tff(c_3369, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_relat_1('#skF_10'))))), inference(splitLeft, [status(thm)], [c_3368])).
% 9.63/3.48  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.63/3.48  tff(c_2464, plain, (![D_359, C_360, B_361, A_362]: (r2_hidden(k1_funct_1(D_359, C_360), B_361) | k1_xboole_0=B_361 | ~r2_hidden(C_360, A_362) | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(A_362, B_361))) | ~v1_funct_2(D_359, A_362, B_361) | ~v1_funct_1(D_359))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.63/3.48  tff(c_6869, plain, (![D_833, A_834, B_835, B_836]: (r2_hidden(k1_funct_1(D_833, A_834), B_835) | k1_xboole_0=B_835 | ~m1_subset_1(D_833, k1_zfmisc_1(k2_zfmisc_1(B_836, B_835))) | ~v1_funct_2(D_833, B_836, B_835) | ~v1_funct_1(D_833) | v1_xboole_0(B_836) | ~m1_subset_1(A_834, B_836))), inference(resolution, [status(thm)], [c_12, c_2464])).
% 9.63/3.48  tff(c_6871, plain, (![A_834]: (r2_hidden(k1_funct_1('#skF_9', A_834), k1_relat_1('#skF_10')) | k1_relat_1('#skF_10')=k1_xboole_0 | ~v1_funct_2('#skF_9', '#skF_7', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_9') | v1_xboole_0('#skF_7') | ~m1_subset_1(A_834, '#skF_7'))), inference(resolution, [status(thm)], [c_3369, c_6869])).
% 9.63/3.48  tff(c_6881, plain, (![A_834]: (r2_hidden(k1_funct_1('#skF_9', A_834), k1_relat_1('#skF_10')) | k1_relat_1('#skF_10')=k1_xboole_0 | v1_xboole_0('#skF_7') | ~m1_subset_1(A_834, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_3050, c_6871])).
% 9.63/3.48  tff(c_6882, plain, (![A_834]: (r2_hidden(k1_funct_1('#skF_9', A_834), k1_relat_1('#skF_10')) | k1_relat_1('#skF_10')=k1_xboole_0 | ~m1_subset_1(A_834, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1177, c_6881])).
% 9.63/3.48  tff(c_7093, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6882])).
% 9.63/3.48  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.63/3.48  tff(c_214, plain, (![C_138, B_139, A_140]: (~v1_xboole_0(C_138) | ~m1_subset_1(B_139, k1_zfmisc_1(C_138)) | ~r2_hidden(A_140, B_139))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.63/3.48  tff(c_228, plain, (![B_143, A_144, A_145]: (~v1_xboole_0(B_143) | ~r2_hidden(A_144, A_145) | ~r1_tarski(A_145, B_143))), inference(resolution, [status(thm)], [c_16, c_214])).
% 9.63/3.48  tff(c_235, plain, (![B_146, A_147]: (~v1_xboole_0(B_146) | ~r1_tarski(A_147, B_146) | v1_xboole_0(A_147))), inference(resolution, [status(thm)], [c_4, c_228])).
% 9.63/3.48  tff(c_249, plain, (~v1_xboole_0(k1_relset_1('#skF_8', '#skF_6', '#skF_10')) | v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_96, c_235])).
% 9.63/3.48  tff(c_380, plain, (~v1_xboole_0(k1_relat_1('#skF_10')) | v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_249])).
% 9.63/3.48  tff(c_381, plain, (~v1_xboole_0(k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_380])).
% 9.63/3.48  tff(c_7106, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7093, c_381])).
% 9.63/3.48  tff(c_7111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7106])).
% 9.63/3.48  tff(c_7115, plain, (![A_846]: (r2_hidden(k1_funct_1('#skF_9', A_846), k1_relat_1('#skF_10')) | ~m1_subset_1(A_846, '#skF_7'))), inference(splitRight, [status(thm)], [c_6882])).
% 9.63/3.48  tff(c_74, plain, (![A_75, B_76, C_78]: (k7_partfun1(A_75, B_76, C_78)=k1_funct_1(B_76, C_78) | ~r2_hidden(C_78, k1_relat_1(B_76)) | ~v1_funct_1(B_76) | ~v5_relat_1(B_76, A_75) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.63/3.48  tff(c_7121, plain, (![A_75, A_846]: (k7_partfun1(A_75, '#skF_10', k1_funct_1('#skF_9', A_846))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', A_846)) | ~v1_funct_1('#skF_10') | ~v5_relat_1('#skF_10', A_75) | ~v1_relat_1('#skF_10') | ~m1_subset_1(A_846, '#skF_7'))), inference(resolution, [status(thm)], [c_7115, c_74])).
% 9.63/3.48  tff(c_7779, plain, (![A_884, A_885]: (k7_partfun1(A_884, '#skF_10', k1_funct_1('#skF_9', A_885))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', A_885)) | ~v5_relat_1('#skF_10', A_884) | ~m1_subset_1(A_885, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_102, c_7121])).
% 9.63/3.48  tff(c_92, plain, (k7_partfun1('#skF_6', '#skF_10', k1_funct_1('#skF_9', '#skF_11'))!=k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_218])).
% 9.63/3.48  tff(c_7785, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~v5_relat_1('#skF_10', '#skF_6') | ~m1_subset_1('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_7779, c_92])).
% 9.63/3.48  tff(c_7805, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_289, c_7785])).
% 9.63/3.48  tff(c_7815, plain, (~m1_subset_1('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4507, c_7805])).
% 9.63/3.48  tff(c_7819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_7815])).
% 9.63/3.48  tff(c_7820, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_3368])).
% 9.63/3.48  tff(c_7886, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7820, c_6])).
% 9.63/3.48  tff(c_7889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_7886])).
% 9.63/3.48  tff(c_7890, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_3049])).
% 9.63/3.48  tff(c_7946, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7890, c_6])).
% 9.63/3.48  tff(c_7949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_7946])).
% 9.63/3.48  tff(c_7951, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1112])).
% 9.63/3.48  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.63/3.48  tff(c_7959, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_7951, c_8])).
% 9.63/3.48  tff(c_7965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_7959])).
% 9.63/3.48  tff(c_7967, plain, (v1_xboole_0(k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_380])).
% 9.63/3.48  tff(c_7975, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_7967, c_8])).
% 9.63/3.48  tff(c_7986, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7975, c_361])).
% 9.63/3.48  tff(c_8194, plain, (![B_905, C_906, A_907]: (k1_xboole_0=B_905 | v1_funct_2(C_906, A_907, B_905) | k1_relset_1(A_907, B_905, C_906)!=A_907 | ~m1_subset_1(C_906, k1_zfmisc_1(k2_zfmisc_1(A_907, B_905))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.63/3.48  tff(c_8204, plain, (k1_xboole_0='#skF_6' | v1_funct_2('#skF_10', '#skF_8', '#skF_6') | k1_relset_1('#skF_8', '#skF_6', '#skF_10')!='#skF_8'), inference(resolution, [status(thm)], [c_100, c_8194])).
% 9.63/3.48  tff(c_8209, plain, (k1_xboole_0='#skF_6' | v1_funct_2('#skF_10', '#skF_8', '#skF_6') | k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7986, c_8204])).
% 9.63/3.48  tff(c_8210, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_8209])).
% 9.63/3.48  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.63/3.48  tff(c_7966, plain, (v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_380])).
% 9.63/3.48  tff(c_8000, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_7966, c_8])).
% 9.63/3.48  tff(c_10906, plain, (![B_1134, D_1135, A_1136, C_1137]: (k1_xboole_0=B_1134 | v1_funct_2(D_1135, A_1136, C_1137) | ~r1_tarski(k2_relset_1(A_1136, B_1134, D_1135), C_1137) | ~m1_subset_1(D_1135, k1_zfmisc_1(k2_zfmisc_1(A_1136, B_1134))) | ~v1_funct_2(D_1135, A_1136, B_1134) | ~v1_funct_1(D_1135))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.63/3.48  tff(c_10908, plain, (![C_1137]: (k1_xboole_0='#skF_8' | v1_funct_2('#skF_9', '#skF_7', C_1137) | ~r1_tarski(k1_xboole_0, C_1137) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_8000, c_10906])).
% 9.63/3.48  tff(c_10910, plain, (![C_1137]: (k1_xboole_0='#skF_8' | v1_funct_2('#skF_9', '#skF_7', C_1137))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_10, c_10908])).
% 9.63/3.48  tff(c_10911, plain, (![C_1137]: (v1_funct_2('#skF_9', '#skF_7', C_1137))), inference(negUnitSimplification, [status(thm)], [c_8210, c_10910])).
% 9.63/3.48  tff(c_11110, plain, (![B_1161, D_1162, A_1163, C_1164]: (k1_xboole_0=B_1161 | m1_subset_1(D_1162, k1_zfmisc_1(k2_zfmisc_1(A_1163, C_1164))) | ~r1_tarski(k2_relset_1(A_1163, B_1161, D_1162), C_1164) | ~m1_subset_1(D_1162, k1_zfmisc_1(k2_zfmisc_1(A_1163, B_1161))) | ~v1_funct_2(D_1162, A_1163, B_1161) | ~v1_funct_1(D_1162))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.63/3.48  tff(c_11112, plain, (![C_1164]: (k1_xboole_0='#skF_8' | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', C_1164))) | ~r1_tarski(k1_xboole_0, C_1164) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_8000, c_11110])).
% 9.63/3.48  tff(c_11114, plain, (![C_1164]: (k1_xboole_0='#skF_8' | m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', C_1164))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_10911, c_104, c_10, c_11112])).
% 9.63/3.48  tff(c_11117, plain, (![C_1165]: (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', C_1165))))), inference(negUnitSimplification, [status(thm)], [c_8210, c_11114])).
% 9.63/3.48  tff(c_64, plain, (![C_74, A_72]: (k1_xboole_0=C_74 | ~v1_funct_2(C_74, A_72, k1_xboole_0) | k1_xboole_0=A_72 | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.63/3.48  tff(c_11127, plain, (k1_xboole_0='#skF_9' | ~v1_funct_2('#skF_9', '#skF_7', k1_xboole_0) | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_11117, c_64])).
% 9.63/3.48  tff(c_11152, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_10911, c_11127])).
% 9.63/3.48  tff(c_11153, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_94, c_11152])).
% 9.63/3.48  tff(c_11230, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11153, c_6])).
% 9.63/3.48  tff(c_178, plain, (![A_133, A_134, B_135]: (v1_relat_1(A_133) | ~r1_tarski(A_133, k2_zfmisc_1(A_134, B_135)))), inference(resolution, [status(thm)], [c_16, c_155])).
% 9.63/3.48  tff(c_193, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_178])).
% 9.63/3.48  tff(c_326, plain, (![A_160, B_161, A_162]: (v5_relat_1(A_160, B_161) | ~r1_tarski(A_160, k2_zfmisc_1(A_162, B_161)))), inference(resolution, [status(thm)], [c_16, c_276])).
% 9.63/3.48  tff(c_346, plain, (![B_161]: (v5_relat_1(k1_xboole_0, B_161))), inference(resolution, [status(thm)], [c_10, c_326])).
% 9.63/3.48  tff(c_253, plain, (![B_148, A_149]: (r1_tarski(k2_relat_1(B_148), A_149) | ~v5_relat_1(B_148, A_149) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.63/3.48  tff(c_125, plain, (![A_122]: (v1_xboole_0(A_122) | r2_hidden('#skF_1'(A_122), A_122))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.63/3.48  tff(c_52, plain, (![B_62, A_61]: (~r1_tarski(B_62, A_61) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.63/3.48  tff(c_132, plain, (![A_122]: (~r1_tarski(A_122, '#skF_1'(A_122)) | v1_xboole_0(A_122))), inference(resolution, [status(thm)], [c_125, c_52])).
% 9.63/3.48  tff(c_8051, plain, (![B_893]: (v1_xboole_0(k2_relat_1(B_893)) | ~v5_relat_1(B_893, '#skF_1'(k2_relat_1(B_893))) | ~v1_relat_1(B_893))), inference(resolution, [status(thm)], [c_253, c_132])).
% 9.63/3.48  tff(c_8055, plain, (v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_346, c_8051])).
% 9.63/3.48  tff(c_8058, plain, (v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_8055])).
% 9.63/3.48  tff(c_8066, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8058, c_8])).
% 9.63/3.48  tff(c_11218, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_11153, c_11153, c_8066])).
% 9.63/3.48  tff(c_8261, plain, (![B_915, A_916, C_917]: (k1_xboole_0=B_915 | k1_relset_1(A_916, B_915, C_917)=A_916 | ~v1_funct_2(C_917, A_916, B_915) | ~m1_subset_1(C_917, k1_zfmisc_1(k2_zfmisc_1(A_916, B_915))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.63/3.48  tff(c_8268, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_104, c_8261])).
% 9.63/3.48  tff(c_8275, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_360, c_8268])).
% 9.63/3.48  tff(c_8276, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_8210, c_8275])).
% 9.63/3.48  tff(c_8030, plain, (![B_888, A_889]: (r2_hidden(k1_funct_1(B_888, A_889), k2_relat_1(B_888)) | ~r2_hidden(A_889, k1_relat_1(B_888)) | ~v1_funct_1(B_888) | ~v1_relat_1(B_888))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.63/3.48  tff(c_8041, plain, (![B_888, A_889]: (~v1_xboole_0(k2_relat_1(B_888)) | ~r2_hidden(A_889, k1_relat_1(B_888)) | ~v1_funct_1(B_888) | ~v1_relat_1(B_888))), inference(resolution, [status(thm)], [c_8030, c_2])).
% 9.63/3.48  tff(c_8284, plain, (![A_889]: (~v1_xboole_0(k2_relat_1('#skF_9')) | ~r2_hidden(A_889, '#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_8276, c_8041])).
% 9.63/3.48  tff(c_8288, plain, (![A_889]: (~v1_xboole_0(k2_relat_1('#skF_9')) | ~r2_hidden(A_889, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_108, c_8284])).
% 9.63/3.48  tff(c_8294, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_8288])).
% 9.63/3.48  tff(c_11249, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11218, c_8294])).
% 9.63/3.48  tff(c_11252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11230, c_11249])).
% 9.63/3.48  tff(c_11255, plain, (![A_1166]: (~r2_hidden(A_1166, '#skF_7'))), inference(splitRight, [status(thm)], [c_8288])).
% 9.63/3.48  tff(c_11265, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_11255])).
% 9.63/3.48  tff(c_11271, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_11265, c_8])).
% 9.63/3.48  tff(c_11276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_11271])).
% 9.63/3.48  tff(c_11278, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_8209])).
% 9.63/3.48  tff(c_11297, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_6])).
% 9.63/3.48  tff(c_11300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_11297])).
% 9.63/3.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.63/3.48  
% 9.63/3.48  Inference rules
% 9.63/3.48  ----------------------
% 9.63/3.48  #Ref     : 0
% 9.63/3.48  #Sup     : 2366
% 9.63/3.48  #Fact    : 0
% 9.63/3.48  #Define  : 0
% 9.63/3.48  #Split   : 34
% 9.63/3.48  #Chain   : 0
% 9.63/3.48  #Close   : 0
% 9.63/3.48  
% 9.63/3.48  Ordering : KBO
% 9.63/3.48  
% 9.63/3.48  Simplification rules
% 9.63/3.48  ----------------------
% 9.63/3.48  #Subsume      : 979
% 9.63/3.48  #Demod        : 2699
% 9.63/3.48  #Tautology    : 452
% 9.63/3.48  #SimpNegUnit  : 125
% 9.63/3.48  #BackRed      : 377
% 9.63/3.48  
% 9.63/3.48  #Partial instantiations: 0
% 9.63/3.48  #Strategies tried      : 1
% 9.63/3.48  
% 9.63/3.48  Timing (in seconds)
% 9.63/3.48  ----------------------
% 9.63/3.49  Preprocessing        : 0.41
% 9.63/3.49  Parsing              : 0.21
% 9.63/3.49  CNF conversion       : 0.04
% 9.63/3.49  Main loop            : 2.21
% 9.63/3.49  Inferencing          : 0.62
% 9.63/3.49  Reduction            : 0.67
% 9.63/3.49  Demodulation         : 0.47
% 9.63/3.49  BG Simplification    : 0.07
% 9.63/3.49  Subsumption          : 0.69
% 9.63/3.49  Abstraction          : 0.09
% 9.63/3.49  MUC search           : 0.00
% 9.63/3.49  Cooper               : 0.00
% 9.63/3.49  Total                : 2.68
% 9.63/3.49  Index Insertion      : 0.00
% 9.63/3.49  Index Deletion       : 0.00
% 9.63/3.49  Index Matching       : 0.00
% 9.63/3.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
