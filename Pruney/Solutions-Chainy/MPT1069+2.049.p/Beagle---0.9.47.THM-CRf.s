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
% DateTime   : Thu Dec  3 10:17:52 EST 2020

% Result     : Theorem 10.43s
% Output     : CNFRefutation 10.43s
% Verified   : 
% Statistics : Number of formulae       :  194 (1379 expanded)
%              Number of leaves         :   51 ( 489 expanded)
%              Depth                    :   23
%              Number of atoms          :  475 (4986 expanded)
%              Number of equality atoms :  117 (1156 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_138,axiom,(
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

tff(f_149,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_176,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_159,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_78,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_30,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_141,plain,(
    ! [B_92,A_93] :
      ( v1_relat_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93))
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_150,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_141])).

tff(c_158,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_150])).

tff(c_82,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_144,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_141])).

tff(c_153,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_144])).

tff(c_88,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_86,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_344,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_361,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_344])).

tff(c_498,plain,(
    ! [B_164,A_165,C_166] :
      ( k1_xboole_0 = B_164
      | k1_relset_1(A_165,B_164,C_166) = A_165
      | ~ v1_funct_2(C_166,A_165,B_164)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_501,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_498])).

tff(c_517,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_361,c_501])).

tff(c_524,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_545,plain,(
    ! [A_167,B_168,C_169] :
      ( k7_partfun1(A_167,B_168,C_169) = k1_funct_1(B_168,C_169)
      | ~ r2_hidden(C_169,k1_relat_1(B_168))
      | ~ v1_funct_1(B_168)
      | ~ v5_relat_1(B_168,A_167)
      | ~ v1_relat_1(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_547,plain,(
    ! [A_167,C_169] :
      ( k7_partfun1(A_167,'#skF_5',C_169) = k1_funct_1('#skF_5',C_169)
      | ~ r2_hidden(C_169,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_167)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_545])).

tff(c_586,plain,(
    ! [A_174,C_175] :
      ( k7_partfun1(A_174,'#skF_5',C_175) = k1_funct_1('#skF_5',C_175)
      | ~ r2_hidden(C_175,'#skF_3')
      | ~ v5_relat_1('#skF_5',A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_88,c_547])).

tff(c_594,plain,(
    ! [A_174,A_7] :
      ( k7_partfun1(A_174,'#skF_5',A_7) = k1_funct_1('#skF_5',A_7)
      | ~ v5_relat_1('#skF_5',A_174)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_7,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_586])).

tff(c_622,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_594])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_625,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_622,c_4])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_625])).

tff(c_631,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_594])).

tff(c_212,plain,(
    ! [C_107,B_108,A_109] :
      ( v5_relat_1(C_107,B_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_229,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_212])).

tff(c_1055,plain,(
    ! [A_235,D_234,C_237,B_233,E_236] :
      ( k1_funct_1(k5_relat_1(D_234,E_236),C_237) = k1_funct_1(E_236,k1_funct_1(D_234,C_237))
      | k1_xboole_0 = B_233
      | ~ r2_hidden(C_237,A_235)
      | ~ v1_funct_1(E_236)
      | ~ v1_relat_1(E_236)
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_233)))
      | ~ v1_funct_2(D_234,A_235,B_233)
      | ~ v1_funct_1(D_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1691,plain,(
    ! [D_328,B_327,A_329,E_330,B_326] :
      ( k1_funct_1(k5_relat_1(D_328,E_330),A_329) = k1_funct_1(E_330,k1_funct_1(D_328,A_329))
      | k1_xboole_0 = B_326
      | ~ v1_funct_1(E_330)
      | ~ v1_relat_1(E_330)
      | ~ m1_subset_1(D_328,k1_zfmisc_1(k2_zfmisc_1(B_327,B_326)))
      | ~ v1_funct_2(D_328,B_327,B_326)
      | ~ v1_funct_1(D_328)
      | v1_xboole_0(B_327)
      | ~ m1_subset_1(A_329,B_327) ) ),
    inference(resolution,[status(thm)],[c_20,c_1055])).

tff(c_1699,plain,(
    ! [E_330,A_329] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_330),A_329) = k1_funct_1(E_330,k1_funct_1('#skF_5',A_329))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_330)
      | ~ v1_relat_1(E_330)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_329,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_84,c_1691])).

tff(c_1713,plain,(
    ! [E_330,A_329] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_330),A_329) = k1_funct_1(E_330,k1_funct_1('#skF_5',A_329))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_330)
      | ~ v1_relat_1(E_330)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_329,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1699])).

tff(c_1714,plain,(
    ! [E_330,A_329] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_330),A_329) = k1_funct_1(E_330,k1_funct_1('#skF_5',A_329))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_330)
      | ~ v1_relat_1(E_330)
      | ~ m1_subset_1(A_329,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_1713])).

tff(c_1722,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1714])).

tff(c_452,plain,(
    ! [B_156,C_157,A_158] :
      ( r2_hidden(k1_funct_1(B_156,C_157),A_158)
      | ~ r2_hidden(C_157,k1_relat_1(B_156))
      | ~ v1_funct_1(B_156)
      | ~ v5_relat_1(B_156,A_158)
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_282,plain,(
    ! [A_120,C_121,B_122] :
      ( m1_subset_1(A_120,C_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(C_121))
      | ~ r2_hidden(A_120,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_290,plain,(
    ! [A_120,A_6] :
      ( m1_subset_1(A_120,A_6)
      | ~ r2_hidden(A_120,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_282])).

tff(c_685,plain,(
    ! [B_187,C_188,A_189] :
      ( m1_subset_1(k1_funct_1(B_187,C_188),A_189)
      | ~ r2_hidden(C_188,k1_relat_1(B_187))
      | ~ v1_funct_1(B_187)
      | ~ v5_relat_1(B_187,k1_xboole_0)
      | ~ v1_relat_1(B_187) ) ),
    inference(resolution,[status(thm)],[c_452,c_290])).

tff(c_687,plain,(
    ! [C_188,A_189] :
      ( m1_subset_1(k1_funct_1('#skF_5',C_188),A_189)
      | ~ r2_hidden(C_188,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_685])).

tff(c_695,plain,(
    ! [C_188,A_189] :
      ( m1_subset_1(k1_funct_1('#skF_5',C_188),A_189)
      | ~ r2_hidden(C_188,'#skF_3')
      | ~ v5_relat_1('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_88,c_687])).

tff(c_698,plain,(
    ~ v5_relat_1('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_695])).

tff(c_1748,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1722,c_698])).

tff(c_1781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_1748])).

tff(c_1782,plain,(
    ! [E_330,A_329] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_330),A_329) = k1_funct_1(E_330,k1_funct_1('#skF_5',A_329))
      | ~ v1_funct_1(E_330)
      | ~ v1_relat_1(E_330)
      | ~ m1_subset_1(A_329,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1714])).

tff(c_363,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_344])).

tff(c_307,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_324,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_307])).

tff(c_76,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_328,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_76])).

tff(c_379,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_328])).

tff(c_957,plain,(
    ! [A_225,D_226,C_221,E_222,F_224,B_223] :
      ( k1_partfun1(A_225,B_223,C_221,D_226,E_222,F_224) = k5_relat_1(E_222,F_224)
      | ~ m1_subset_1(F_224,k1_zfmisc_1(k2_zfmisc_1(C_221,D_226)))
      | ~ v1_funct_1(F_224)
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_225,B_223)))
      | ~ v1_funct_1(E_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_971,plain,(
    ! [A_225,B_223,E_222] :
      ( k1_partfun1(A_225,B_223,'#skF_4','#skF_2',E_222,'#skF_6') = k5_relat_1(E_222,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_225,B_223)))
      | ~ v1_funct_1(E_222) ) ),
    inference(resolution,[status(thm)],[c_80,c_957])).

tff(c_1017,plain,(
    ! [A_230,B_231,E_232] :
      ( k1_partfun1(A_230,B_231,'#skF_4','#skF_2',E_232,'#skF_6') = k5_relat_1(E_232,'#skF_6')
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231)))
      | ~ v1_funct_1(E_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_971])).

tff(c_1024,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_1017])).

tff(c_1041,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1024])).

tff(c_1783,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1714])).

tff(c_1150,plain,(
    ! [B_252,C_253,D_251,E_250,A_249] :
      ( k1_partfun1(A_249,B_252,B_252,C_253,D_251,E_250) = k8_funct_2(A_249,B_252,C_253,D_251,E_250)
      | k1_xboole_0 = B_252
      | ~ r1_tarski(k2_relset_1(A_249,B_252,D_251),k1_relset_1(B_252,C_253,E_250))
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(B_252,C_253)))
      | ~ v1_funct_1(E_250)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_252)))
      | ~ v1_funct_2(D_251,A_249,B_252)
      | ~ v1_funct_1(D_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1168,plain,(
    ! [C_253,E_250] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_253,'#skF_5',E_250) = k8_funct_2('#skF_3','#skF_4',C_253,'#skF_5',E_250)
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_253,E_250))
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_253)))
      | ~ v1_funct_1(E_250)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_1150])).

tff(c_1181,plain,(
    ! [C_253,E_250] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_253,'#skF_5',E_250) = k8_funct_2('#skF_3','#skF_4',C_253,'#skF_5',E_250)
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_253,E_250))
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_253)))
      | ~ v1_funct_1(E_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_1168])).

tff(c_2442,plain,(
    ! [C_407,E_408] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_407,'#skF_5',E_408) = k8_funct_2('#skF_3','#skF_4',C_407,'#skF_5',E_408)
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_407,E_408))
      | ~ m1_subset_1(E_408,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_407)))
      | ~ v1_funct_1(E_408) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1783,c_1181])).

tff(c_2445,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_2442])).

tff(c_2454,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_379,c_1041,c_2445])).

tff(c_231,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_212])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( v5_relat_1(B_16,A_15)
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_382,plain,
    ( v5_relat_1('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_379,c_26])).

tff(c_387,plain,(
    v5_relat_1('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_382])).

tff(c_32,plain,(
    ! [B_20,C_22,A_19] :
      ( r2_hidden(k1_funct_1(B_20,C_22),A_19)
      | ~ r2_hidden(C_22,k1_relat_1(B_20))
      | ~ v1_funct_1(B_20)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1347,plain,(
    ! [A_297,B_298,B_299,C_300] :
      ( k7_partfun1(A_297,B_298,k1_funct_1(B_299,C_300)) = k1_funct_1(B_298,k1_funct_1(B_299,C_300))
      | ~ v1_funct_1(B_298)
      | ~ v5_relat_1(B_298,A_297)
      | ~ v1_relat_1(B_298)
      | ~ r2_hidden(C_300,k1_relat_1(B_299))
      | ~ v1_funct_1(B_299)
      | ~ v5_relat_1(B_299,k1_relat_1(B_298))
      | ~ v1_relat_1(B_299) ) ),
    inference(resolution,[status(thm)],[c_32,c_545])).

tff(c_1351,plain,(
    ! [A_297,B_298,C_300] :
      ( k7_partfun1(A_297,B_298,k1_funct_1('#skF_5',C_300)) = k1_funct_1(B_298,k1_funct_1('#skF_5',C_300))
      | ~ v1_funct_1(B_298)
      | ~ v5_relat_1(B_298,A_297)
      | ~ v1_relat_1(B_298)
      | ~ r2_hidden(C_300,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k1_relat_1(B_298))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_1347])).

tff(c_1371,plain,(
    ! [A_303,B_304,C_305] :
      ( k7_partfun1(A_303,B_304,k1_funct_1('#skF_5',C_305)) = k1_funct_1(B_304,k1_funct_1('#skF_5',C_305))
      | ~ v1_funct_1(B_304)
      | ~ v5_relat_1(B_304,A_303)
      | ~ v1_relat_1(B_304)
      | ~ r2_hidden(C_305,'#skF_3')
      | ~ v5_relat_1('#skF_5',k1_relat_1(B_304)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_88,c_1351])).

tff(c_1375,plain,(
    ! [A_303,C_305] :
      ( k7_partfun1(A_303,'#skF_6',k1_funct_1('#skF_5',C_305)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_305))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_303)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_305,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_387,c_1371])).

tff(c_1381,plain,(
    ! [A_306,C_307] :
      ( k7_partfun1(A_306,'#skF_6',k1_funct_1('#skF_5',C_307)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_307))
      | ~ v5_relat_1('#skF_6',A_306)
      | ~ r2_hidden(C_307,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_82,c_1375])).

tff(c_72,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1387,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_72])).

tff(c_1393,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_1387])).

tff(c_1395,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1393])).

tff(c_1398,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1395])).

tff(c_1401,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1398])).

tff(c_1403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_1401])).

tff(c_1404,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1393])).

tff(c_2460,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2454,c_1404])).

tff(c_2468,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1782,c_2460])).

tff(c_2472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_158,c_82,c_2468])).

tff(c_2489,plain,(
    ! [C_411,A_412] :
      ( m1_subset_1(k1_funct_1('#skF_5',C_411),A_412)
      | ~ r2_hidden(C_411,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_695])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_258,plain,(
    ! [C_117,B_118,A_119] :
      ( v1_xboole_0(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(B_118,A_119)))
      | ~ v1_xboole_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_271,plain,(
    ! [C_117] :
      ( v1_xboole_0(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_258])).

tff(c_279,plain,(
    ! [C_117] :
      ( v1_xboole_0(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_271])).

tff(c_2572,plain,(
    ! [C_413] :
      ( v1_xboole_0(k1_funct_1('#skF_5',C_413))
      | ~ r2_hidden(C_413,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2489,c_279])).

tff(c_2577,plain,(
    ! [C_414] :
      ( k1_funct_1('#skF_5',C_414) = k1_xboole_0
      | ~ r2_hidden(C_414,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2572,c_4])).

tff(c_2585,plain,(
    ! [A_7] :
      ( k1_funct_1('#skF_5',A_7) = k1_xboole_0
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_7,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_2577])).

tff(c_2590,plain,(
    ! [A_415] :
      ( k1_funct_1('#skF_5',A_415) = k1_xboole_0
      | ~ m1_subset_1(A_415,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_2585])).

tff(c_2599,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_2590])).

tff(c_3082,plain,(
    ! [B_442,C_446,A_444,D_443,E_445] :
      ( k1_funct_1(k5_relat_1(D_443,E_445),C_446) = k1_funct_1(E_445,k1_funct_1(D_443,C_446))
      | k1_xboole_0 = B_442
      | ~ r2_hidden(C_446,A_444)
      | ~ v1_funct_1(E_445)
      | ~ v1_relat_1(E_445)
      | ~ m1_subset_1(D_443,k1_zfmisc_1(k2_zfmisc_1(A_444,B_442)))
      | ~ v1_funct_2(D_443,A_444,B_442)
      | ~ v1_funct_1(D_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_6138,plain,(
    ! [A_657,E_656,B_655,D_658,B_654] :
      ( k1_funct_1(k5_relat_1(D_658,E_656),A_657) = k1_funct_1(E_656,k1_funct_1(D_658,A_657))
      | k1_xboole_0 = B_654
      | ~ v1_funct_1(E_656)
      | ~ v1_relat_1(E_656)
      | ~ m1_subset_1(D_658,k1_zfmisc_1(k2_zfmisc_1(B_655,B_654)))
      | ~ v1_funct_2(D_658,B_655,B_654)
      | ~ v1_funct_1(D_658)
      | v1_xboole_0(B_655)
      | ~ m1_subset_1(A_657,B_655) ) ),
    inference(resolution,[status(thm)],[c_20,c_3082])).

tff(c_6149,plain,(
    ! [E_656,A_657] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_656),A_657) = k1_funct_1(E_656,k1_funct_1('#skF_5',A_657))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_656)
      | ~ v1_relat_1(E_656)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_657,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_84,c_6138])).

tff(c_6161,plain,(
    ! [E_656,A_657] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_656),A_657) = k1_funct_1(E_656,k1_funct_1('#skF_5',A_657))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_656)
      | ~ v1_relat_1(E_656)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_657,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_6149])).

tff(c_6162,plain,(
    ! [E_656,A_657] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_656),A_657) = k1_funct_1(E_656,k1_funct_1('#skF_5',A_657))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_656)
      | ~ v1_relat_1(E_656)
      | ~ m1_subset_1(A_657,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_6161])).

tff(c_6176,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6162])).

tff(c_6274,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6176,c_2])).

tff(c_6278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_6274])).

tff(c_6279,plain,(
    ! [E_656,A_657] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_656),A_657) = k1_funct_1(E_656,k1_funct_1('#skF_5',A_657))
      | ~ v1_funct_1(E_656)
      | ~ v1_relat_1(E_656)
      | ~ m1_subset_1(A_657,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_6162])).

tff(c_2798,plain,(
    ! [C_421,D_426,F_424,A_425,E_422,B_423] :
      ( k1_partfun1(A_425,B_423,C_421,D_426,E_422,F_424) = k5_relat_1(E_422,F_424)
      | ~ m1_subset_1(F_424,k1_zfmisc_1(k2_zfmisc_1(C_421,D_426)))
      | ~ v1_funct_1(F_424)
      | ~ m1_subset_1(E_422,k1_zfmisc_1(k2_zfmisc_1(A_425,B_423)))
      | ~ v1_funct_1(E_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2812,plain,(
    ! [A_425,B_423,E_422] :
      ( k1_partfun1(A_425,B_423,'#skF_4','#skF_2',E_422,'#skF_6') = k5_relat_1(E_422,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_422,k1_zfmisc_1(k2_zfmisc_1(A_425,B_423)))
      | ~ v1_funct_1(E_422) ) ),
    inference(resolution,[status(thm)],[c_80,c_2798])).

tff(c_2831,plain,(
    ! [A_429,B_430,E_431] :
      ( k1_partfun1(A_429,B_430,'#skF_4','#skF_2',E_431,'#skF_6') = k5_relat_1(E_431,'#skF_6')
      | ~ m1_subset_1(E_431,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430)))
      | ~ v1_funct_1(E_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2812])).

tff(c_2842,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_2831])).

tff(c_2856,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2842])).

tff(c_6280,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6162])).

tff(c_3214,plain,(
    ! [C_461,E_458,D_459,B_460,A_457] :
      ( k1_partfun1(A_457,B_460,B_460,C_461,D_459,E_458) = k8_funct_2(A_457,B_460,C_461,D_459,E_458)
      | k1_xboole_0 = B_460
      | ~ r1_tarski(k2_relset_1(A_457,B_460,D_459),k1_relset_1(B_460,C_461,E_458))
      | ~ m1_subset_1(E_458,k1_zfmisc_1(k2_zfmisc_1(B_460,C_461)))
      | ~ v1_funct_1(E_458)
      | ~ m1_subset_1(D_459,k1_zfmisc_1(k2_zfmisc_1(A_457,B_460)))
      | ~ v1_funct_2(D_459,A_457,B_460)
      | ~ v1_funct_1(D_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3241,plain,(
    ! [C_461,E_458] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_461,'#skF_5',E_458) = k8_funct_2('#skF_3','#skF_4',C_461,'#skF_5',E_458)
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_461,E_458))
      | ~ m1_subset_1(E_458,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_461)))
      | ~ v1_funct_1(E_458)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_3214])).

tff(c_3258,plain,(
    ! [C_461,E_458] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_461,'#skF_5',E_458) = k8_funct_2('#skF_3','#skF_4',C_461,'#skF_5',E_458)
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_461,E_458))
      | ~ m1_subset_1(E_458,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_461)))
      | ~ v1_funct_1(E_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_3241])).

tff(c_11839,plain,(
    ! [C_790,E_791] :
      ( k1_partfun1('#skF_3','#skF_4','#skF_4',C_790,'#skF_5',E_791) = k8_funct_2('#skF_3','#skF_4',C_790,'#skF_5',E_791)
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',C_790,E_791))
      | ~ m1_subset_1(E_791,k1_zfmisc_1(k2_zfmisc_1('#skF_4',C_790)))
      | ~ v1_funct_1(E_791) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6280,c_3258])).

tff(c_11854,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_11839])).

tff(c_11863,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_379,c_2856,c_11854])).

tff(c_2473,plain,(
    ! [C_188,A_189] :
      ( m1_subset_1(k1_funct_1('#skF_5',C_188),A_189)
      | ~ r2_hidden(C_188,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_695])).

tff(c_2608,plain,(
    ! [A_189] :
      ( m1_subset_1(k1_xboole_0,A_189)
      | ~ r2_hidden('#skF_7','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2599,c_2473])).

tff(c_2637,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2608])).

tff(c_2640,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2637])).

tff(c_2643,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2640])).

tff(c_2645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_2643])).

tff(c_2647,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2608])).

tff(c_2611,plain,(
    ! [A_19] :
      ( r2_hidden(k1_xboole_0,A_19)
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_19)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2599,c_32])).

tff(c_2616,plain,(
    ! [A_19] :
      ( r2_hidden(k1_xboole_0,A_19)
      | ~ r2_hidden('#skF_7','#skF_3')
      | ~ v5_relat_1('#skF_5',A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_88,c_524,c_2611])).

tff(c_2994,plain,(
    ! [A_437] :
      ( r2_hidden(k1_xboole_0,A_437)
      | ~ v5_relat_1('#skF_5',A_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_2616])).

tff(c_3009,plain,(
    r2_hidden(k1_xboole_0,k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_387,c_2994])).

tff(c_58,plain,(
    ! [A_45,B_46,C_48] :
      ( k7_partfun1(A_45,B_46,C_48) = k1_funct_1(B_46,C_48)
      | ~ r2_hidden(C_48,k1_relat_1(B_46))
      | ~ v1_funct_1(B_46)
      | ~ v5_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_3023,plain,(
    ! [A_45] :
      ( k7_partfun1(A_45,'#skF_6',k1_xboole_0) = k1_funct_1('#skF_6',k1_xboole_0)
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_45)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3009,c_58])).

tff(c_3065,plain,(
    ! [A_441] :
      ( k7_partfun1(A_441,'#skF_6',k1_xboole_0) = k1_funct_1('#skF_6',k1_xboole_0)
      | ~ v5_relat_1('#skF_6',A_441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_82,c_3023])).

tff(c_3076,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_xboole_0) = k1_funct_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_231,c_3065])).

tff(c_2601,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k7_partfun1('#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2599,c_72])).

tff(c_3077,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_2601])).

tff(c_11869,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11863,c_3077])).

tff(c_11876,plain,
    ( k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1('#skF_6',k1_xboole_0)
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6279,c_11869])).

tff(c_11879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_158,c_82,c_2599,c_11876])).

tff(c_11880,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_11908,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11880,c_2])).

tff(c_11911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_11908])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:53:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.43/3.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.43/3.72  
% 10.43/3.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.43/3.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.43/3.72  
% 10.43/3.72  %Foreground sorts:
% 10.43/3.72  
% 10.43/3.72  
% 10.43/3.72  %Background operators:
% 10.43/3.72  
% 10.43/3.72  
% 10.43/3.72  %Foreground operators:
% 10.43/3.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.43/3.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.43/3.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.43/3.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.43/3.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.43/3.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.43/3.72  tff('#skF_7', type, '#skF_7': $i).
% 10.43/3.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.43/3.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.43/3.72  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 10.43/3.72  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.43/3.72  tff('#skF_5', type, '#skF_5': $i).
% 10.43/3.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.43/3.72  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 10.43/3.72  tff('#skF_6', type, '#skF_6': $i).
% 10.43/3.72  tff('#skF_2', type, '#skF_2': $i).
% 10.43/3.72  tff('#skF_3', type, '#skF_3': $i).
% 10.43/3.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.43/3.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.43/3.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.43/3.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.43/3.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.43/3.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.43/3.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.43/3.72  tff('#skF_4', type, '#skF_4': $i).
% 10.43/3.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.43/3.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.43/3.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.43/3.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.43/3.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.43/3.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.43/3.72  
% 10.43/3.75  tff(f_219, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 10.43/3.75  tff(f_71, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.43/3.75  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.43/3.75  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.43/3.75  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.43/3.75  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.43/3.75  tff(f_149, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 10.43/3.75  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.43/3.75  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.43/3.75  tff(f_176, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 10.43/3.75  tff(f_82, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 10.43/3.75  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.43/3.75  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 10.43/3.75  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.43/3.75  tff(f_159, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.43/3.75  tff(f_120, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 10.43/3.75  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.43/3.75  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.43/3.75  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.43/3.75  tff(f_95, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 10.43/3.75  tff(c_90, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_78, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_30, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.43/3.75  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_141, plain, (![B_92, A_93]: (v1_relat_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.43/3.75  tff(c_150, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_141])).
% 10.43/3.75  tff(c_158, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_150])).
% 10.43/3.75  tff(c_82, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_74, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_20, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.43/3.75  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_144, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_141])).
% 10.43/3.75  tff(c_153, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_144])).
% 10.43/3.75  tff(c_88, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_86, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_344, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.43/3.75  tff(c_361, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_344])).
% 10.43/3.75  tff(c_498, plain, (![B_164, A_165, C_166]: (k1_xboole_0=B_164 | k1_relset_1(A_165, B_164, C_166)=A_165 | ~v1_funct_2(C_166, A_165, B_164) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.43/3.75  tff(c_501, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_498])).
% 10.43/3.75  tff(c_517, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_361, c_501])).
% 10.43/3.75  tff(c_524, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_517])).
% 10.43/3.75  tff(c_545, plain, (![A_167, B_168, C_169]: (k7_partfun1(A_167, B_168, C_169)=k1_funct_1(B_168, C_169) | ~r2_hidden(C_169, k1_relat_1(B_168)) | ~v1_funct_1(B_168) | ~v5_relat_1(B_168, A_167) | ~v1_relat_1(B_168))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.43/3.75  tff(c_547, plain, (![A_167, C_169]: (k7_partfun1(A_167, '#skF_5', C_169)=k1_funct_1('#skF_5', C_169) | ~r2_hidden(C_169, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_167) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_524, c_545])).
% 10.43/3.75  tff(c_586, plain, (![A_174, C_175]: (k7_partfun1(A_174, '#skF_5', C_175)=k1_funct_1('#skF_5', C_175) | ~r2_hidden(C_175, '#skF_3') | ~v5_relat_1('#skF_5', A_174))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_88, c_547])).
% 10.43/3.75  tff(c_594, plain, (![A_174, A_7]: (k7_partfun1(A_174, '#skF_5', A_7)=k1_funct_1('#skF_5', A_7) | ~v5_relat_1('#skF_5', A_174) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_7, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_586])).
% 10.43/3.75  tff(c_622, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_594])).
% 10.43/3.75  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.43/3.75  tff(c_625, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_622, c_4])).
% 10.43/3.75  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_625])).
% 10.43/3.75  tff(c_631, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_594])).
% 10.43/3.75  tff(c_212, plain, (![C_107, B_108, A_109]: (v5_relat_1(C_107, B_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.43/3.75  tff(c_229, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_212])).
% 10.43/3.75  tff(c_1055, plain, (![A_235, D_234, C_237, B_233, E_236]: (k1_funct_1(k5_relat_1(D_234, E_236), C_237)=k1_funct_1(E_236, k1_funct_1(D_234, C_237)) | k1_xboole_0=B_233 | ~r2_hidden(C_237, A_235) | ~v1_funct_1(E_236) | ~v1_relat_1(E_236) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_233))) | ~v1_funct_2(D_234, A_235, B_233) | ~v1_funct_1(D_234))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.43/3.75  tff(c_1691, plain, (![D_328, B_327, A_329, E_330, B_326]: (k1_funct_1(k5_relat_1(D_328, E_330), A_329)=k1_funct_1(E_330, k1_funct_1(D_328, A_329)) | k1_xboole_0=B_326 | ~v1_funct_1(E_330) | ~v1_relat_1(E_330) | ~m1_subset_1(D_328, k1_zfmisc_1(k2_zfmisc_1(B_327, B_326))) | ~v1_funct_2(D_328, B_327, B_326) | ~v1_funct_1(D_328) | v1_xboole_0(B_327) | ~m1_subset_1(A_329, B_327))), inference(resolution, [status(thm)], [c_20, c_1055])).
% 10.43/3.75  tff(c_1699, plain, (![E_330, A_329]: (k1_funct_1(k5_relat_1('#skF_5', E_330), A_329)=k1_funct_1(E_330, k1_funct_1('#skF_5', A_329)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_330) | ~v1_relat_1(E_330) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_329, '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_1691])).
% 10.43/3.75  tff(c_1713, plain, (![E_330, A_329]: (k1_funct_1(k5_relat_1('#skF_5', E_330), A_329)=k1_funct_1(E_330, k1_funct_1('#skF_5', A_329)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_330) | ~v1_relat_1(E_330) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_329, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_1699])).
% 10.43/3.75  tff(c_1714, plain, (![E_330, A_329]: (k1_funct_1(k5_relat_1('#skF_5', E_330), A_329)=k1_funct_1(E_330, k1_funct_1('#skF_5', A_329)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_330) | ~v1_relat_1(E_330) | ~m1_subset_1(A_329, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_631, c_1713])).
% 10.43/3.75  tff(c_1722, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1714])).
% 10.43/3.75  tff(c_452, plain, (![B_156, C_157, A_158]: (r2_hidden(k1_funct_1(B_156, C_157), A_158) | ~r2_hidden(C_157, k1_relat_1(B_156)) | ~v1_funct_1(B_156) | ~v5_relat_1(B_156, A_158) | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.43/3.75  tff(c_18, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.43/3.75  tff(c_282, plain, (![A_120, C_121, B_122]: (m1_subset_1(A_120, C_121) | ~m1_subset_1(B_122, k1_zfmisc_1(C_121)) | ~r2_hidden(A_120, B_122))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.43/3.75  tff(c_290, plain, (![A_120, A_6]: (m1_subset_1(A_120, A_6) | ~r2_hidden(A_120, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_282])).
% 10.43/3.75  tff(c_685, plain, (![B_187, C_188, A_189]: (m1_subset_1(k1_funct_1(B_187, C_188), A_189) | ~r2_hidden(C_188, k1_relat_1(B_187)) | ~v1_funct_1(B_187) | ~v5_relat_1(B_187, k1_xboole_0) | ~v1_relat_1(B_187))), inference(resolution, [status(thm)], [c_452, c_290])).
% 10.43/3.75  tff(c_687, plain, (![C_188, A_189]: (m1_subset_1(k1_funct_1('#skF_5', C_188), A_189) | ~r2_hidden(C_188, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_524, c_685])).
% 10.43/3.75  tff(c_695, plain, (![C_188, A_189]: (m1_subset_1(k1_funct_1('#skF_5', C_188), A_189) | ~r2_hidden(C_188, '#skF_3') | ~v5_relat_1('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_88, c_687])).
% 10.43/3.75  tff(c_698, plain, (~v5_relat_1('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_695])).
% 10.43/3.75  tff(c_1748, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1722, c_698])).
% 10.43/3.75  tff(c_1781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_1748])).
% 10.43/3.75  tff(c_1782, plain, (![E_330, A_329]: (k1_funct_1(k5_relat_1('#skF_5', E_330), A_329)=k1_funct_1(E_330, k1_funct_1('#skF_5', A_329)) | ~v1_funct_1(E_330) | ~v1_relat_1(E_330) | ~m1_subset_1(A_329, '#skF_3'))), inference(splitRight, [status(thm)], [c_1714])).
% 10.43/3.75  tff(c_363, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_344])).
% 10.43/3.75  tff(c_307, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.43/3.75  tff(c_324, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_307])).
% 10.43/3.75  tff(c_76, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_328, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_76])).
% 10.43/3.75  tff(c_379, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_328])).
% 10.43/3.75  tff(c_957, plain, (![A_225, D_226, C_221, E_222, F_224, B_223]: (k1_partfun1(A_225, B_223, C_221, D_226, E_222, F_224)=k5_relat_1(E_222, F_224) | ~m1_subset_1(F_224, k1_zfmisc_1(k2_zfmisc_1(C_221, D_226))) | ~v1_funct_1(F_224) | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))) | ~v1_funct_1(E_222))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.43/3.75  tff(c_971, plain, (![A_225, B_223, E_222]: (k1_partfun1(A_225, B_223, '#skF_4', '#skF_2', E_222, '#skF_6')=k5_relat_1(E_222, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))) | ~v1_funct_1(E_222))), inference(resolution, [status(thm)], [c_80, c_957])).
% 10.43/3.75  tff(c_1017, plain, (![A_230, B_231, E_232]: (k1_partfun1(A_230, B_231, '#skF_4', '#skF_2', E_232, '#skF_6')=k5_relat_1(E_232, '#skF_6') | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))) | ~v1_funct_1(E_232))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_971])).
% 10.43/3.75  tff(c_1024, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_1017])).
% 10.43/3.75  tff(c_1041, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1024])).
% 10.43/3.75  tff(c_1783, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1714])).
% 10.43/3.75  tff(c_1150, plain, (![B_252, C_253, D_251, E_250, A_249]: (k1_partfun1(A_249, B_252, B_252, C_253, D_251, E_250)=k8_funct_2(A_249, B_252, C_253, D_251, E_250) | k1_xboole_0=B_252 | ~r1_tarski(k2_relset_1(A_249, B_252, D_251), k1_relset_1(B_252, C_253, E_250)) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(B_252, C_253))) | ~v1_funct_1(E_250) | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_252))) | ~v1_funct_2(D_251, A_249, B_252) | ~v1_funct_1(D_251))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.43/3.75  tff(c_1168, plain, (![C_253, E_250]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_253, '#skF_5', E_250)=k8_funct_2('#skF_3', '#skF_4', C_253, '#skF_5', E_250) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_253, E_250)) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_253))) | ~v1_funct_1(E_250) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_1150])).
% 10.43/3.75  tff(c_1181, plain, (![C_253, E_250]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_253, '#skF_5', E_250)=k8_funct_2('#skF_3', '#skF_4', C_253, '#skF_5', E_250) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_253, E_250)) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_253))) | ~v1_funct_1(E_250))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_1168])).
% 10.43/3.75  tff(c_2442, plain, (![C_407, E_408]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_407, '#skF_5', E_408)=k8_funct_2('#skF_3', '#skF_4', C_407, '#skF_5', E_408) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_407, E_408)) | ~m1_subset_1(E_408, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_407))) | ~v1_funct_1(E_408))), inference(negUnitSimplification, [status(thm)], [c_1783, c_1181])).
% 10.43/3.75  tff(c_2445, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_363, c_2442])).
% 10.43/3.75  tff(c_2454, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_379, c_1041, c_2445])).
% 10.43/3.75  tff(c_231, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_212])).
% 10.43/3.75  tff(c_26, plain, (![B_16, A_15]: (v5_relat_1(B_16, A_15) | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.43/3.75  tff(c_382, plain, (v5_relat_1('#skF_5', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_379, c_26])).
% 10.43/3.75  tff(c_387, plain, (v5_relat_1('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_382])).
% 10.43/3.75  tff(c_32, plain, (![B_20, C_22, A_19]: (r2_hidden(k1_funct_1(B_20, C_22), A_19) | ~r2_hidden(C_22, k1_relat_1(B_20)) | ~v1_funct_1(B_20) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.43/3.75  tff(c_1347, plain, (![A_297, B_298, B_299, C_300]: (k7_partfun1(A_297, B_298, k1_funct_1(B_299, C_300))=k1_funct_1(B_298, k1_funct_1(B_299, C_300)) | ~v1_funct_1(B_298) | ~v5_relat_1(B_298, A_297) | ~v1_relat_1(B_298) | ~r2_hidden(C_300, k1_relat_1(B_299)) | ~v1_funct_1(B_299) | ~v5_relat_1(B_299, k1_relat_1(B_298)) | ~v1_relat_1(B_299))), inference(resolution, [status(thm)], [c_32, c_545])).
% 10.43/3.75  tff(c_1351, plain, (![A_297, B_298, C_300]: (k7_partfun1(A_297, B_298, k1_funct_1('#skF_5', C_300))=k1_funct_1(B_298, k1_funct_1('#skF_5', C_300)) | ~v1_funct_1(B_298) | ~v5_relat_1(B_298, A_297) | ~v1_relat_1(B_298) | ~r2_hidden(C_300, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', k1_relat_1(B_298)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_524, c_1347])).
% 10.43/3.75  tff(c_1371, plain, (![A_303, B_304, C_305]: (k7_partfun1(A_303, B_304, k1_funct_1('#skF_5', C_305))=k1_funct_1(B_304, k1_funct_1('#skF_5', C_305)) | ~v1_funct_1(B_304) | ~v5_relat_1(B_304, A_303) | ~v1_relat_1(B_304) | ~r2_hidden(C_305, '#skF_3') | ~v5_relat_1('#skF_5', k1_relat_1(B_304)))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_88, c_1351])).
% 10.43/3.75  tff(c_1375, plain, (![A_303, C_305]: (k7_partfun1(A_303, '#skF_6', k1_funct_1('#skF_5', C_305))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_305)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_303) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_305, '#skF_3'))), inference(resolution, [status(thm)], [c_387, c_1371])).
% 10.43/3.75  tff(c_1381, plain, (![A_306, C_307]: (k7_partfun1(A_306, '#skF_6', k1_funct_1('#skF_5', C_307))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_307)) | ~v5_relat_1('#skF_6', A_306) | ~r2_hidden(C_307, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_82, c_1375])).
% 10.43/3.75  tff(c_72, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 10.43/3.75  tff(c_1387, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1381, c_72])).
% 10.43/3.75  tff(c_1393, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_1387])).
% 10.43/3.75  tff(c_1395, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_1393])).
% 10.43/3.75  tff(c_1398, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_1395])).
% 10.43/3.75  tff(c_1401, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1398])).
% 10.43/3.75  tff(c_1403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_631, c_1401])).
% 10.43/3.75  tff(c_1404, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1393])).
% 10.43/3.75  tff(c_2460, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2454, c_1404])).
% 10.43/3.75  tff(c_2468, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1782, c_2460])).
% 10.43/3.75  tff(c_2472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_158, c_82, c_2468])).
% 10.43/3.75  tff(c_2489, plain, (![C_411, A_412]: (m1_subset_1(k1_funct_1('#skF_5', C_411), A_412) | ~r2_hidden(C_411, '#skF_3'))), inference(splitRight, [status(thm)], [c_695])).
% 10.43/3.75  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.43/3.75  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.43/3.75  tff(c_258, plain, (![C_117, B_118, A_119]: (v1_xboole_0(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(B_118, A_119))) | ~v1_xboole_0(A_119))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.43/3.75  tff(c_271, plain, (![C_117]: (v1_xboole_0(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_258])).
% 10.43/3.75  tff(c_279, plain, (![C_117]: (v1_xboole_0(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_271])).
% 10.43/3.75  tff(c_2572, plain, (![C_413]: (v1_xboole_0(k1_funct_1('#skF_5', C_413)) | ~r2_hidden(C_413, '#skF_3'))), inference(resolution, [status(thm)], [c_2489, c_279])).
% 10.43/3.75  tff(c_2577, plain, (![C_414]: (k1_funct_1('#skF_5', C_414)=k1_xboole_0 | ~r2_hidden(C_414, '#skF_3'))), inference(resolution, [status(thm)], [c_2572, c_4])).
% 10.43/3.75  tff(c_2585, plain, (![A_7]: (k1_funct_1('#skF_5', A_7)=k1_xboole_0 | v1_xboole_0('#skF_3') | ~m1_subset_1(A_7, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_2577])).
% 10.43/3.75  tff(c_2590, plain, (![A_415]: (k1_funct_1('#skF_5', A_415)=k1_xboole_0 | ~m1_subset_1(A_415, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_631, c_2585])).
% 10.43/3.75  tff(c_2599, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_2590])).
% 10.43/3.75  tff(c_3082, plain, (![B_442, C_446, A_444, D_443, E_445]: (k1_funct_1(k5_relat_1(D_443, E_445), C_446)=k1_funct_1(E_445, k1_funct_1(D_443, C_446)) | k1_xboole_0=B_442 | ~r2_hidden(C_446, A_444) | ~v1_funct_1(E_445) | ~v1_relat_1(E_445) | ~m1_subset_1(D_443, k1_zfmisc_1(k2_zfmisc_1(A_444, B_442))) | ~v1_funct_2(D_443, A_444, B_442) | ~v1_funct_1(D_443))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.43/3.75  tff(c_6138, plain, (![A_657, E_656, B_655, D_658, B_654]: (k1_funct_1(k5_relat_1(D_658, E_656), A_657)=k1_funct_1(E_656, k1_funct_1(D_658, A_657)) | k1_xboole_0=B_654 | ~v1_funct_1(E_656) | ~v1_relat_1(E_656) | ~m1_subset_1(D_658, k1_zfmisc_1(k2_zfmisc_1(B_655, B_654))) | ~v1_funct_2(D_658, B_655, B_654) | ~v1_funct_1(D_658) | v1_xboole_0(B_655) | ~m1_subset_1(A_657, B_655))), inference(resolution, [status(thm)], [c_20, c_3082])).
% 10.43/3.75  tff(c_6149, plain, (![E_656, A_657]: (k1_funct_1(k5_relat_1('#skF_5', E_656), A_657)=k1_funct_1(E_656, k1_funct_1('#skF_5', A_657)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_656) | ~v1_relat_1(E_656) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_657, '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_6138])).
% 10.43/3.75  tff(c_6161, plain, (![E_656, A_657]: (k1_funct_1(k5_relat_1('#skF_5', E_656), A_657)=k1_funct_1(E_656, k1_funct_1('#skF_5', A_657)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_656) | ~v1_relat_1(E_656) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_657, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_6149])).
% 10.43/3.75  tff(c_6162, plain, (![E_656, A_657]: (k1_funct_1(k5_relat_1('#skF_5', E_656), A_657)=k1_funct_1(E_656, k1_funct_1('#skF_5', A_657)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_656) | ~v1_relat_1(E_656) | ~m1_subset_1(A_657, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_631, c_6161])).
% 10.43/3.75  tff(c_6176, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_6162])).
% 10.43/3.75  tff(c_6274, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6176, c_2])).
% 10.43/3.75  tff(c_6278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_6274])).
% 10.43/3.75  tff(c_6279, plain, (![E_656, A_657]: (k1_funct_1(k5_relat_1('#skF_5', E_656), A_657)=k1_funct_1(E_656, k1_funct_1('#skF_5', A_657)) | ~v1_funct_1(E_656) | ~v1_relat_1(E_656) | ~m1_subset_1(A_657, '#skF_3'))), inference(splitRight, [status(thm)], [c_6162])).
% 10.43/3.75  tff(c_2798, plain, (![C_421, D_426, F_424, A_425, E_422, B_423]: (k1_partfun1(A_425, B_423, C_421, D_426, E_422, F_424)=k5_relat_1(E_422, F_424) | ~m1_subset_1(F_424, k1_zfmisc_1(k2_zfmisc_1(C_421, D_426))) | ~v1_funct_1(F_424) | ~m1_subset_1(E_422, k1_zfmisc_1(k2_zfmisc_1(A_425, B_423))) | ~v1_funct_1(E_422))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.43/3.75  tff(c_2812, plain, (![A_425, B_423, E_422]: (k1_partfun1(A_425, B_423, '#skF_4', '#skF_2', E_422, '#skF_6')=k5_relat_1(E_422, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_422, k1_zfmisc_1(k2_zfmisc_1(A_425, B_423))) | ~v1_funct_1(E_422))), inference(resolution, [status(thm)], [c_80, c_2798])).
% 10.43/3.75  tff(c_2831, plain, (![A_429, B_430, E_431]: (k1_partfun1(A_429, B_430, '#skF_4', '#skF_2', E_431, '#skF_6')=k5_relat_1(E_431, '#skF_6') | ~m1_subset_1(E_431, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))) | ~v1_funct_1(E_431))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2812])).
% 10.43/3.75  tff(c_2842, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_2831])).
% 10.43/3.75  tff(c_2856, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2842])).
% 10.43/3.75  tff(c_6280, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_6162])).
% 10.43/3.75  tff(c_3214, plain, (![C_461, E_458, D_459, B_460, A_457]: (k1_partfun1(A_457, B_460, B_460, C_461, D_459, E_458)=k8_funct_2(A_457, B_460, C_461, D_459, E_458) | k1_xboole_0=B_460 | ~r1_tarski(k2_relset_1(A_457, B_460, D_459), k1_relset_1(B_460, C_461, E_458)) | ~m1_subset_1(E_458, k1_zfmisc_1(k2_zfmisc_1(B_460, C_461))) | ~v1_funct_1(E_458) | ~m1_subset_1(D_459, k1_zfmisc_1(k2_zfmisc_1(A_457, B_460))) | ~v1_funct_2(D_459, A_457, B_460) | ~v1_funct_1(D_459))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.43/3.75  tff(c_3241, plain, (![C_461, E_458]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_461, '#skF_5', E_458)=k8_funct_2('#skF_3', '#skF_4', C_461, '#skF_5', E_458) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_461, E_458)) | ~m1_subset_1(E_458, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_461))) | ~v1_funct_1(E_458) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_3214])).
% 10.43/3.75  tff(c_3258, plain, (![C_461, E_458]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_461, '#skF_5', E_458)=k8_funct_2('#skF_3', '#skF_4', C_461, '#skF_5', E_458) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_461, E_458)) | ~m1_subset_1(E_458, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_461))) | ~v1_funct_1(E_458))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_3241])).
% 10.43/3.75  tff(c_11839, plain, (![C_790, E_791]: (k1_partfun1('#skF_3', '#skF_4', '#skF_4', C_790, '#skF_5', E_791)=k8_funct_2('#skF_3', '#skF_4', C_790, '#skF_5', E_791) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', C_790, E_791)) | ~m1_subset_1(E_791, k1_zfmisc_1(k2_zfmisc_1('#skF_4', C_790))) | ~v1_funct_1(E_791))), inference(negUnitSimplification, [status(thm)], [c_6280, c_3258])).
% 10.43/3.75  tff(c_11854, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_363, c_11839])).
% 10.43/3.75  tff(c_11863, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_379, c_2856, c_11854])).
% 10.43/3.75  tff(c_2473, plain, (![C_188, A_189]: (m1_subset_1(k1_funct_1('#skF_5', C_188), A_189) | ~r2_hidden(C_188, '#skF_3'))), inference(splitRight, [status(thm)], [c_695])).
% 10.43/3.75  tff(c_2608, plain, (![A_189]: (m1_subset_1(k1_xboole_0, A_189) | ~r2_hidden('#skF_7', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2599, c_2473])).
% 10.43/3.75  tff(c_2637, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_2608])).
% 10.43/3.75  tff(c_2640, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_2637])).
% 10.43/3.75  tff(c_2643, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2640])).
% 10.43/3.75  tff(c_2645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_631, c_2643])).
% 10.43/3.75  tff(c_2647, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_2608])).
% 10.43/3.75  tff(c_2611, plain, (![A_19]: (r2_hidden(k1_xboole_0, A_19) | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_19) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2599, c_32])).
% 10.43/3.75  tff(c_2616, plain, (![A_19]: (r2_hidden(k1_xboole_0, A_19) | ~r2_hidden('#skF_7', '#skF_3') | ~v5_relat_1('#skF_5', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_88, c_524, c_2611])).
% 10.43/3.75  tff(c_2994, plain, (![A_437]: (r2_hidden(k1_xboole_0, A_437) | ~v5_relat_1('#skF_5', A_437))), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_2616])).
% 10.43/3.75  tff(c_3009, plain, (r2_hidden(k1_xboole_0, k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_387, c_2994])).
% 10.43/3.75  tff(c_58, plain, (![A_45, B_46, C_48]: (k7_partfun1(A_45, B_46, C_48)=k1_funct_1(B_46, C_48) | ~r2_hidden(C_48, k1_relat_1(B_46)) | ~v1_funct_1(B_46) | ~v5_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.43/3.75  tff(c_3023, plain, (![A_45]: (k7_partfun1(A_45, '#skF_6', k1_xboole_0)=k1_funct_1('#skF_6', k1_xboole_0) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_45) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3009, c_58])).
% 10.43/3.75  tff(c_3065, plain, (![A_441]: (k7_partfun1(A_441, '#skF_6', k1_xboole_0)=k1_funct_1('#skF_6', k1_xboole_0) | ~v5_relat_1('#skF_6', A_441))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_82, c_3023])).
% 10.43/3.75  tff(c_3076, plain, (k7_partfun1('#skF_2', '#skF_6', k1_xboole_0)=k1_funct_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_231, c_3065])).
% 10.43/3.75  tff(c_2601, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k7_partfun1('#skF_2', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2599, c_72])).
% 10.43/3.75  tff(c_3077, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3076, c_2601])).
% 10.43/3.75  tff(c_11869, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11863, c_3077])).
% 10.43/3.75  tff(c_11876, plain, (k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1('#skF_6', k1_xboole_0) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6279, c_11869])).
% 10.43/3.75  tff(c_11879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_158, c_82, c_2599, c_11876])).
% 10.43/3.75  tff(c_11880, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_517])).
% 10.43/3.75  tff(c_11908, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11880, c_2])).
% 10.43/3.75  tff(c_11911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_11908])).
% 10.43/3.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.43/3.75  
% 10.43/3.75  Inference rules
% 10.43/3.75  ----------------------
% 10.43/3.75  #Ref     : 3
% 10.43/3.75  #Sup     : 2500
% 10.43/3.75  #Fact    : 0
% 10.43/3.75  #Define  : 0
% 10.43/3.75  #Split   : 37
% 10.43/3.75  #Chain   : 0
% 10.43/3.75  #Close   : 0
% 10.43/3.75  
% 10.43/3.75  Ordering : KBO
% 10.43/3.75  
% 10.43/3.75  Simplification rules
% 10.43/3.75  ----------------------
% 10.43/3.75  #Subsume      : 1018
% 10.43/3.75  #Demod        : 3840
% 10.43/3.75  #Tautology    : 756
% 10.43/3.75  #SimpNegUnit  : 531
% 10.43/3.75  #BackRed      : 230
% 10.43/3.75  
% 10.43/3.75  #Partial instantiations: 0
% 10.43/3.75  #Strategies tried      : 1
% 10.43/3.75  
% 10.43/3.75  Timing (in seconds)
% 10.43/3.75  ----------------------
% 10.43/3.75  Preprocessing        : 0.40
% 10.43/3.75  Parsing              : 0.21
% 10.43/3.76  CNF conversion       : 0.03
% 10.43/3.76  Main loop            : 2.56
% 10.43/3.76  Inferencing          : 0.69
% 10.43/3.76  Reduction            : 0.95
% 10.43/3.76  Demodulation         : 0.70
% 10.43/3.76  BG Simplification    : 0.09
% 10.43/3.76  Subsumption          : 0.68
% 10.43/3.76  Abstraction          : 0.13
% 10.43/3.76  MUC search           : 0.00
% 10.43/3.76  Cooper               : 0.00
% 10.43/3.76  Total                : 3.02
% 10.43/3.76  Index Insertion      : 0.00
% 10.43/3.76  Index Deletion       : 0.00
% 10.43/3.76  Index Matching       : 0.00
% 10.43/3.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
