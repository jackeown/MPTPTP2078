%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:40 EST 2020

% Result     : Theorem 8.89s
% Output     : CNFRefutation 9.03s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 395 expanded)
%              Number of leaves         :   51 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          :  240 ( 957 expanded)
%              Number of equality atoms :   28 ( 168 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_9 > #skF_13 > #skF_7 > #skF_4 > #skF_5 > #skF_3 > #skF_2 > #skF_8 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_189,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_180,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_163,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(c_116,plain,(
    r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1338,plain,(
    ! [A_259,B_260,D_261] :
      ( '#skF_9'(A_259,B_260,k1_funct_2(A_259,B_260),D_261) = D_261
      | ~ r2_hidden(D_261,k1_funct_2(A_259,B_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1349,plain,(
    '#skF_9'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_116,c_1338])).

tff(c_1519,plain,(
    ! [A_283,B_284,D_285] :
      ( v1_relat_1('#skF_9'(A_283,B_284,k1_funct_2(A_283,B_284),D_285))
      | ~ r2_hidden(D_285,k1_funct_2(A_283,B_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1522,plain,
    ( v1_relat_1('#skF_13')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_1519])).

tff(c_1524,plain,(
    v1_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_1522])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1766,plain,(
    ! [A_297,B_298,D_299] :
      ( k1_relat_1('#skF_9'(A_297,B_298,k1_funct_2(A_297,B_298),D_299)) = A_297
      | ~ r2_hidden(D_299,k1_funct_2(A_297,B_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1787,plain,
    ( k1_relat_1('#skF_13') = '#skF_11'
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_1766])).

tff(c_1791,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_1787])).

tff(c_1985,plain,(
    ! [A_312,B_313,D_314] :
      ( r1_tarski(k2_relat_1('#skF_9'(A_312,B_313,k1_funct_2(A_312,B_313),D_314)),B_313)
      | ~ r2_hidden(D_314,k1_funct_2(A_312,B_313)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2020,plain,
    ( r1_tarski(k2_relat_1('#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_1985])).

tff(c_2031,plain,(
    r1_tarski(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_2020])).

tff(c_3629,plain,(
    ! [C_400,A_401,B_402] :
      ( m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402)))
      | ~ r1_tarski(k2_relat_1(C_400),B_402)
      | ~ r1_tarski(k1_relat_1(C_400),A_401)
      | ~ v1_relat_1(C_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_114,plain,
    ( ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12')))
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_152,plain,(
    ~ v1_funct_1('#skF_13') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_750,plain,(
    ! [A_170,B_171,D_172] :
      ( '#skF_9'(A_170,B_171,k1_funct_2(A_170,B_171),D_172) = D_172
      | ~ r2_hidden(D_172,k1_funct_2(A_170,B_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_761,plain,(
    '#skF_9'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_116,c_750])).

tff(c_781,plain,(
    ! [A_177,B_178,D_179] :
      ( v1_funct_1('#skF_9'(A_177,B_178,k1_funct_2(A_177,B_178),D_179))
      | ~ r2_hidden(D_179,k1_funct_2(A_177,B_178)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_784,plain,
    ( v1_funct_1('#skF_13')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_781])).

tff(c_786,plain,(
    v1_funct_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_784])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_786])).

tff(c_789,plain,
    ( ~ v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_798,plain,(
    ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_789])).

tff(c_3653,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_13'),'#skF_12')
    | ~ r1_tarski(k1_relat_1('#skF_13'),'#skF_11')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_3629,c_798])).

tff(c_3682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1524,c_18,c_1791,c_2031,c_3653])).

tff(c_3684,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_3719,plain,(
    ! [C_411,A_412,B_413] :
      ( v1_relat_1(C_411)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3736,plain,(
    v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_3684,c_3719])).

tff(c_790,plain,(
    v1_funct_1('#skF_13') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_4187,plain,(
    ! [A_461,B_462,D_463] :
      ( '#skF_9'(A_461,B_462,k1_funct_2(A_461,B_462),D_463) = D_463
      | ~ r2_hidden(D_463,k1_funct_2(A_461,B_462)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4198,plain,(
    '#skF_9'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_116,c_4187])).

tff(c_4490,plain,(
    ! [A_506,B_507,D_508] :
      ( k1_relat_1('#skF_9'(A_506,B_507,k1_funct_2(A_506,B_507),D_508)) = A_506
      | ~ r2_hidden(D_508,k1_funct_2(A_506,B_507)) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4511,plain,
    ( k1_relat_1('#skF_13') = '#skF_11'
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4198,c_4490])).

tff(c_4515,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_4511])).

tff(c_10467,plain,(
    ! [C_814,B_815] :
      ( r2_hidden('#skF_10'(k1_relat_1(C_814),B_815,C_814),k1_relat_1(C_814))
      | v1_funct_2(C_814,k1_relat_1(C_814),B_815)
      | ~ v1_funct_1(C_814)
      | ~ v1_relat_1(C_814) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_10483,plain,(
    ! [B_815] :
      ( r2_hidden('#skF_10'('#skF_11',B_815,'#skF_13'),k1_relat_1('#skF_13'))
      | v1_funct_2('#skF_13',k1_relat_1('#skF_13'),B_815)
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4515,c_10467])).

tff(c_10497,plain,(
    ! [B_815] :
      ( r2_hidden('#skF_10'('#skF_11',B_815,'#skF_13'),'#skF_11')
      | v1_funct_2('#skF_13','#skF_11',B_815) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3736,c_790,c_4515,c_4515,c_10483])).

tff(c_96,plain,(
    ! [A_72] :
      ( m1_subset_1(A_72,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_72),k2_relat_1(A_72))))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4525,plain,
    ( m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',k2_relat_1('#skF_13'))))
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_4515,c_96])).

tff(c_4536,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',k2_relat_1('#skF_13')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3736,c_790,c_4525])).

tff(c_40,plain,(
    ! [C_31,B_29,A_28] :
      ( v1_xboole_0(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(B_29,A_28)))
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4577,plain,
    ( v1_xboole_0('#skF_13')
    | ~ v1_xboole_0(k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_4536,c_40])).

tff(c_4584,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_4577])).

tff(c_3683,plain,(
    ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_5030,plain,(
    ! [C_537,A_538,B_539] :
      ( v1_funct_2(C_537,A_538,B_539)
      | ~ v1_partfun1(C_537,A_538)
      | ~ v1_funct_1(C_537)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5054,plain,
    ( v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_partfun1('#skF_13','#skF_11')
    | ~ v1_funct_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_3684,c_5030])).

tff(c_5075,plain,
    ( v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_partfun1('#skF_13','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_5054])).

tff(c_5076,plain,(
    ~ v1_partfun1('#skF_13','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_3683,c_5075])).

tff(c_98,plain,(
    ! [A_72] :
      ( v1_funct_2(A_72,k1_relat_1(A_72),k2_relat_1(A_72))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4528,plain,
    ( v1_funct_2('#skF_13','#skF_11',k2_relat_1('#skF_13'))
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_4515,c_98])).

tff(c_4538,plain,(
    v1_funct_2('#skF_13','#skF_11',k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3736,c_790,c_4528])).

tff(c_7665,plain,(
    ! [C_658,A_659,B_660] :
      ( v1_partfun1(C_658,A_659)
      | ~ v1_funct_2(C_658,A_659,B_660)
      | ~ v1_funct_1(C_658)
      | ~ m1_subset_1(C_658,k1_zfmisc_1(k2_zfmisc_1(A_659,B_660)))
      | v1_xboole_0(B_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_7685,plain,
    ( v1_partfun1('#skF_13','#skF_11')
    | ~ v1_funct_2('#skF_13','#skF_11',k2_relat_1('#skF_13'))
    | ~ v1_funct_1('#skF_13')
    | v1_xboole_0(k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_4536,c_7665])).

tff(c_7710,plain,
    ( v1_partfun1('#skF_13','#skF_11')
    | v1_xboole_0(k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_4538,c_7685])).

tff(c_7712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4584,c_5076,c_7710])).

tff(c_7713,plain,(
    v1_xboole_0('#skF_13') ),
    inference(splitRight,[status(thm)],[c_4577])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3738,plain,(
    ! [A_414,B_415] :
      ( r2_hidden('#skF_2'(A_414,B_415),A_414)
      | r1_tarski(A_414,B_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3748,plain,(
    ! [A_414,B_415] :
      ( ~ v1_xboole_0(A_414)
      | r1_tarski(A_414,B_415) ) ),
    inference(resolution,[status(thm)],[c_3738,c_2])).

tff(c_3749,plain,(
    ! [A_416,B_417] :
      ( ~ v1_xboole_0(A_416)
      | r1_tarski(A_416,B_417) ) ),
    inference(resolution,[status(thm)],[c_3738,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3854,plain,(
    ! [B_432,A_433] :
      ( B_432 = A_433
      | ~ r1_tarski(B_432,A_433)
      | ~ v1_xboole_0(A_433) ) ),
    inference(resolution,[status(thm)],[c_3749,c_14])).

tff(c_3872,plain,(
    ! [B_434,A_435] :
      ( B_434 = A_435
      | ~ v1_xboole_0(B_434)
      | ~ v1_xboole_0(A_435) ) ),
    inference(resolution,[status(thm)],[c_3748,c_3854])).

tff(c_3875,plain,(
    ! [A_435] :
      ( k1_xboole_0 = A_435
      | ~ v1_xboole_0(A_435) ) ),
    inference(resolution,[status(thm)],[c_12,c_3872])).

tff(c_7723,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_7713,c_3875])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1('#skF_3'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3999,plain,(
    ! [C_451,B_452,A_453] :
      ( v1_xboole_0(C_451)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(B_452,A_453)))
      | ~ v1_xboole_0(A_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4013,plain,(
    ! [C_451] :
      ( v1_xboole_0(C_451)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3999])).

tff(c_4028,plain,(
    ! [C_454] :
      ( v1_xboole_0(C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4013])).

tff(c_4045,plain,(
    v1_xboole_0('#skF_3'(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_26,c_4028])).

tff(c_4058,plain,(
    '#skF_3'(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4045,c_3875])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3965,plain,(
    ! [C_444,B_445,A_446] :
      ( v5_relat_1(C_444,B_445)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_446,B_445))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4202,plain,(
    ! [A_465,B_466] : v5_relat_1('#skF_3'(k1_zfmisc_1(k2_zfmisc_1(A_465,B_466))),B_466) ),
    inference(resolution,[status(thm)],[c_26,c_3965])).

tff(c_4211,plain,(
    ! [B_13] : v5_relat_1('#skF_3'(k1_zfmisc_1(k1_xboole_0)),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4202])).

tff(c_4213,plain,(
    ! [B_13] : v5_relat_1(k1_xboole_0,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4058,c_4211])).

tff(c_7732,plain,(
    ! [B_13] : v5_relat_1('#skF_13',B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7723,c_4213])).

tff(c_32,plain,(
    ! [B_19,C_21,A_18] :
      ( r2_hidden(k1_funct_1(B_19,C_21),A_18)
      | ~ r2_hidden(C_21,k1_relat_1(B_19))
      | ~ v1_funct_1(B_19)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11373,plain,(
    ! [C_838,B_839] :
      ( ~ r2_hidden(k1_funct_1(C_838,'#skF_10'(k1_relat_1(C_838),B_839,C_838)),B_839)
      | v1_funct_2(C_838,k1_relat_1(C_838),B_839)
      | ~ v1_funct_1(C_838)
      | ~ v1_relat_1(C_838) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_11383,plain,(
    ! [B_839] :
      ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_10'('#skF_11',B_839,'#skF_13')),B_839)
      | v1_funct_2('#skF_13',k1_relat_1('#skF_13'),B_839)
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4515,c_11373])).

tff(c_11885,plain,(
    ! [B_844] :
      ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_10'('#skF_11',B_844,'#skF_13')),B_844)
      | v1_funct_2('#skF_13','#skF_11',B_844) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3736,c_790,c_4515,c_11383])).

tff(c_11889,plain,(
    ! [A_18] :
      ( v1_funct_2('#skF_13','#skF_11',A_18)
      | ~ r2_hidden('#skF_10'('#skF_11',A_18,'#skF_13'),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v5_relat_1('#skF_13',A_18)
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_32,c_11885])).

tff(c_12148,plain,(
    ! [A_847] :
      ( v1_funct_2('#skF_13','#skF_11',A_847)
      | ~ r2_hidden('#skF_10'('#skF_11',A_847,'#skF_13'),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3736,c_7732,c_790,c_4515,c_11889])).

tff(c_12152,plain,(
    ! [B_815] : v1_funct_2('#skF_13','#skF_11',B_815) ),
    inference(resolution,[status(thm)],[c_10497,c_12148])).

tff(c_12159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12152,c_3683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:42:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.89/2.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.03/2.94  
% 9.03/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.03/2.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_9 > #skF_13 > #skF_7 > #skF_4 > #skF_5 > #skF_3 > #skF_2 > #skF_8 > #skF_12 > #skF_10
% 9.03/2.94  
% 9.03/2.94  %Foreground sorts:
% 9.03/2.94  
% 9.03/2.94  
% 9.03/2.94  %Background operators:
% 9.03/2.94  
% 9.03/2.94  
% 9.03/2.94  %Foreground operators:
% 9.03/2.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.03/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.03/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.03/2.94  tff('#skF_11', type, '#skF_11': $i).
% 9.03/2.94  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.03/2.94  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.03/2.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.03/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.03/2.94  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 9.03/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.03/2.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.03/2.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.03/2.94  tff('#skF_13', type, '#skF_13': $i).
% 9.03/2.94  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.03/2.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.03/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.03/2.94  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.03/2.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.03/2.94  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 9.03/2.94  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 9.03/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.03/2.94  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 9.03/2.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.03/2.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.03/2.94  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.03/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.03/2.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.03/2.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.03/2.94  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 9.03/2.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.03/2.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.03/2.94  tff('#skF_12', type, '#skF_12': $i).
% 9.03/2.94  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 9.03/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.03/2.94  
% 9.03/2.96  tff(f_189, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 9.03/2.96  tff(f_153, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 9.03/2.96  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.03/2.96  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 9.03/2.96  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.03/2.96  tff(f_180, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 9.03/2.96  tff(f_163, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.03/2.96  tff(f_86, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.03/2.96  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 9.03/2.96  tff(f_137, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 9.03/2.96  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.03/2.96  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.03/2.96  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.03/2.96  tff(f_54, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 9.03/2.96  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.03/2.96  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.03/2.96  tff(f_69, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 9.03/2.96  tff(c_116, plain, (r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 9.03/2.96  tff(c_1338, plain, (![A_259, B_260, D_261]: ('#skF_9'(A_259, B_260, k1_funct_2(A_259, B_260), D_261)=D_261 | ~r2_hidden(D_261, k1_funct_2(A_259, B_260)))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.03/2.96  tff(c_1349, plain, ('#skF_9'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_116, c_1338])).
% 9.03/2.96  tff(c_1519, plain, (![A_283, B_284, D_285]: (v1_relat_1('#skF_9'(A_283, B_284, k1_funct_2(A_283, B_284), D_285)) | ~r2_hidden(D_285, k1_funct_2(A_283, B_284)))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.03/2.96  tff(c_1522, plain, (v1_relat_1('#skF_13') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_1519])).
% 9.03/2.96  tff(c_1524, plain, (v1_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_1522])).
% 9.03/2.96  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.03/2.96  tff(c_1766, plain, (![A_297, B_298, D_299]: (k1_relat_1('#skF_9'(A_297, B_298, k1_funct_2(A_297, B_298), D_299))=A_297 | ~r2_hidden(D_299, k1_funct_2(A_297, B_298)))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.03/2.96  tff(c_1787, plain, (k1_relat_1('#skF_13')='#skF_11' | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_1766])).
% 9.03/2.96  tff(c_1791, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_1787])).
% 9.03/2.96  tff(c_1985, plain, (![A_312, B_313, D_314]: (r1_tarski(k2_relat_1('#skF_9'(A_312, B_313, k1_funct_2(A_312, B_313), D_314)), B_313) | ~r2_hidden(D_314, k1_funct_2(A_312, B_313)))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.03/2.96  tff(c_2020, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_1985])).
% 9.03/2.96  tff(c_2031, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_2020])).
% 9.03/2.96  tff(c_3629, plain, (![C_400, A_401, B_402]: (m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))) | ~r1_tarski(k2_relat_1(C_400), B_402) | ~r1_tarski(k1_relat_1(C_400), A_401) | ~v1_relat_1(C_400))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.03/2.96  tff(c_114, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12'))) | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_189])).
% 9.03/2.96  tff(c_152, plain, (~v1_funct_1('#skF_13')), inference(splitLeft, [status(thm)], [c_114])).
% 9.03/2.96  tff(c_750, plain, (![A_170, B_171, D_172]: ('#skF_9'(A_170, B_171, k1_funct_2(A_170, B_171), D_172)=D_172 | ~r2_hidden(D_172, k1_funct_2(A_170, B_171)))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.03/2.96  tff(c_761, plain, ('#skF_9'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_116, c_750])).
% 9.03/2.96  tff(c_781, plain, (![A_177, B_178, D_179]: (v1_funct_1('#skF_9'(A_177, B_178, k1_funct_2(A_177, B_178), D_179)) | ~r2_hidden(D_179, k1_funct_2(A_177, B_178)))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.03/2.96  tff(c_784, plain, (v1_funct_1('#skF_13') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_761, c_781])).
% 9.03/2.96  tff(c_786, plain, (v1_funct_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_784])).
% 9.03/2.96  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_786])).
% 9.03/2.96  tff(c_789, plain, (~v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitRight, [status(thm)], [c_114])).
% 9.03/2.96  tff(c_798, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitLeft, [status(thm)], [c_789])).
% 9.03/2.96  tff(c_3653, plain, (~r1_tarski(k2_relat_1('#skF_13'), '#skF_12') | ~r1_tarski(k1_relat_1('#skF_13'), '#skF_11') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_3629, c_798])).
% 9.03/2.96  tff(c_3682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1524, c_18, c_1791, c_2031, c_3653])).
% 9.03/2.96  tff(c_3684, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitRight, [status(thm)], [c_789])).
% 9.03/2.96  tff(c_3719, plain, (![C_411, A_412, B_413]: (v1_relat_1(C_411) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.03/2.96  tff(c_3736, plain, (v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_3684, c_3719])).
% 9.03/2.96  tff(c_790, plain, (v1_funct_1('#skF_13')), inference(splitRight, [status(thm)], [c_114])).
% 9.03/2.96  tff(c_4187, plain, (![A_461, B_462, D_463]: ('#skF_9'(A_461, B_462, k1_funct_2(A_461, B_462), D_463)=D_463 | ~r2_hidden(D_463, k1_funct_2(A_461, B_462)))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.03/2.96  tff(c_4198, plain, ('#skF_9'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_116, c_4187])).
% 9.03/2.96  tff(c_4490, plain, (![A_506, B_507, D_508]: (k1_relat_1('#skF_9'(A_506, B_507, k1_funct_2(A_506, B_507), D_508))=A_506 | ~r2_hidden(D_508, k1_funct_2(A_506, B_507)))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.03/2.96  tff(c_4511, plain, (k1_relat_1('#skF_13')='#skF_11' | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_4198, c_4490])).
% 9.03/2.96  tff(c_4515, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_4511])).
% 9.03/2.96  tff(c_10467, plain, (![C_814, B_815]: (r2_hidden('#skF_10'(k1_relat_1(C_814), B_815, C_814), k1_relat_1(C_814)) | v1_funct_2(C_814, k1_relat_1(C_814), B_815) | ~v1_funct_1(C_814) | ~v1_relat_1(C_814))), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.03/2.96  tff(c_10483, plain, (![B_815]: (r2_hidden('#skF_10'('#skF_11', B_815, '#skF_13'), k1_relat_1('#skF_13')) | v1_funct_2('#skF_13', k1_relat_1('#skF_13'), B_815) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_4515, c_10467])).
% 9.03/2.96  tff(c_10497, plain, (![B_815]: (r2_hidden('#skF_10'('#skF_11', B_815, '#skF_13'), '#skF_11') | v1_funct_2('#skF_13', '#skF_11', B_815))), inference(demodulation, [status(thm), theory('equality')], [c_3736, c_790, c_4515, c_4515, c_10483])).
% 9.03/2.96  tff(c_96, plain, (![A_72]: (m1_subset_1(A_72, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_72), k2_relat_1(A_72)))) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.03/2.96  tff(c_4525, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', k2_relat_1('#skF_13')))) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_4515, c_96])).
% 9.03/2.96  tff(c_4536, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', k2_relat_1('#skF_13'))))), inference(demodulation, [status(thm), theory('equality')], [c_3736, c_790, c_4525])).
% 9.03/2.96  tff(c_40, plain, (![C_31, B_29, A_28]: (v1_xboole_0(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(B_29, A_28))) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.03/2.96  tff(c_4577, plain, (v1_xboole_0('#skF_13') | ~v1_xboole_0(k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_4536, c_40])).
% 9.03/2.96  tff(c_4584, plain, (~v1_xboole_0(k2_relat_1('#skF_13'))), inference(splitLeft, [status(thm)], [c_4577])).
% 9.03/2.96  tff(c_3683, plain, (~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(splitRight, [status(thm)], [c_789])).
% 9.03/2.96  tff(c_5030, plain, (![C_537, A_538, B_539]: (v1_funct_2(C_537, A_538, B_539) | ~v1_partfun1(C_537, A_538) | ~v1_funct_1(C_537) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.03/2.96  tff(c_5054, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_partfun1('#skF_13', '#skF_11') | ~v1_funct_1('#skF_13')), inference(resolution, [status(thm)], [c_3684, c_5030])).
% 9.03/2.96  tff(c_5075, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_partfun1('#skF_13', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_5054])).
% 9.03/2.96  tff(c_5076, plain, (~v1_partfun1('#skF_13', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_3683, c_5075])).
% 9.03/2.96  tff(c_98, plain, (![A_72]: (v1_funct_2(A_72, k1_relat_1(A_72), k2_relat_1(A_72)) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.03/2.96  tff(c_4528, plain, (v1_funct_2('#skF_13', '#skF_11', k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_4515, c_98])).
% 9.03/2.96  tff(c_4538, plain, (v1_funct_2('#skF_13', '#skF_11', k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_3736, c_790, c_4528])).
% 9.03/2.96  tff(c_7665, plain, (![C_658, A_659, B_660]: (v1_partfun1(C_658, A_659) | ~v1_funct_2(C_658, A_659, B_660) | ~v1_funct_1(C_658) | ~m1_subset_1(C_658, k1_zfmisc_1(k2_zfmisc_1(A_659, B_660))) | v1_xboole_0(B_660))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.03/2.96  tff(c_7685, plain, (v1_partfun1('#skF_13', '#skF_11') | ~v1_funct_2('#skF_13', '#skF_11', k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | v1_xboole_0(k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_4536, c_7665])).
% 9.03/2.96  tff(c_7710, plain, (v1_partfun1('#skF_13', '#skF_11') | v1_xboole_0(k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_790, c_4538, c_7685])).
% 9.03/2.96  tff(c_7712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4584, c_5076, c_7710])).
% 9.03/2.96  tff(c_7713, plain, (v1_xboole_0('#skF_13')), inference(splitRight, [status(thm)], [c_4577])).
% 9.03/2.96  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.03/2.96  tff(c_3738, plain, (![A_414, B_415]: (r2_hidden('#skF_2'(A_414, B_415), A_414) | r1_tarski(A_414, B_415))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.03/2.96  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.03/2.96  tff(c_3748, plain, (![A_414, B_415]: (~v1_xboole_0(A_414) | r1_tarski(A_414, B_415))), inference(resolution, [status(thm)], [c_3738, c_2])).
% 9.03/2.96  tff(c_3749, plain, (![A_416, B_417]: (~v1_xboole_0(A_416) | r1_tarski(A_416, B_417))), inference(resolution, [status(thm)], [c_3738, c_2])).
% 9.03/2.96  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.03/2.96  tff(c_3854, plain, (![B_432, A_433]: (B_432=A_433 | ~r1_tarski(B_432, A_433) | ~v1_xboole_0(A_433))), inference(resolution, [status(thm)], [c_3749, c_14])).
% 9.03/2.96  tff(c_3872, plain, (![B_434, A_435]: (B_434=A_435 | ~v1_xboole_0(B_434) | ~v1_xboole_0(A_435))), inference(resolution, [status(thm)], [c_3748, c_3854])).
% 9.03/2.96  tff(c_3875, plain, (![A_435]: (k1_xboole_0=A_435 | ~v1_xboole_0(A_435))), inference(resolution, [status(thm)], [c_12, c_3872])).
% 9.03/2.96  tff(c_7723, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_7713, c_3875])).
% 9.03/2.96  tff(c_26, plain, (![A_14]: (m1_subset_1('#skF_3'(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.03/2.96  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.03/2.96  tff(c_3999, plain, (![C_451, B_452, A_453]: (v1_xboole_0(C_451) | ~m1_subset_1(C_451, k1_zfmisc_1(k2_zfmisc_1(B_452, A_453))) | ~v1_xboole_0(A_453))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.03/2.96  tff(c_4013, plain, (![C_451]: (v1_xboole_0(C_451) | ~m1_subset_1(C_451, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3999])).
% 9.03/2.96  tff(c_4028, plain, (![C_454]: (v1_xboole_0(C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4013])).
% 9.03/2.96  tff(c_4045, plain, (v1_xboole_0('#skF_3'(k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_26, c_4028])).
% 9.03/2.96  tff(c_4058, plain, ('#skF_3'(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_4045, c_3875])).
% 9.03/2.96  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.03/2.96  tff(c_3965, plain, (![C_444, B_445, A_446]: (v5_relat_1(C_444, B_445) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_446, B_445))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.03/2.96  tff(c_4202, plain, (![A_465, B_466]: (v5_relat_1('#skF_3'(k1_zfmisc_1(k2_zfmisc_1(A_465, B_466))), B_466))), inference(resolution, [status(thm)], [c_26, c_3965])).
% 9.03/2.96  tff(c_4211, plain, (![B_13]: (v5_relat_1('#skF_3'(k1_zfmisc_1(k1_xboole_0)), B_13))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4202])).
% 9.03/2.96  tff(c_4213, plain, (![B_13]: (v5_relat_1(k1_xboole_0, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_4058, c_4211])).
% 9.03/2.96  tff(c_7732, plain, (![B_13]: (v5_relat_1('#skF_13', B_13))), inference(demodulation, [status(thm), theory('equality')], [c_7723, c_4213])).
% 9.03/2.96  tff(c_32, plain, (![B_19, C_21, A_18]: (r2_hidden(k1_funct_1(B_19, C_21), A_18) | ~r2_hidden(C_21, k1_relat_1(B_19)) | ~v1_funct_1(B_19) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.03/2.96  tff(c_11373, plain, (![C_838, B_839]: (~r2_hidden(k1_funct_1(C_838, '#skF_10'(k1_relat_1(C_838), B_839, C_838)), B_839) | v1_funct_2(C_838, k1_relat_1(C_838), B_839) | ~v1_funct_1(C_838) | ~v1_relat_1(C_838))), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.03/2.96  tff(c_11383, plain, (![B_839]: (~r2_hidden(k1_funct_1('#skF_13', '#skF_10'('#skF_11', B_839, '#skF_13')), B_839) | v1_funct_2('#skF_13', k1_relat_1('#skF_13'), B_839) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_4515, c_11373])).
% 9.03/2.96  tff(c_11885, plain, (![B_844]: (~r2_hidden(k1_funct_1('#skF_13', '#skF_10'('#skF_11', B_844, '#skF_13')), B_844) | v1_funct_2('#skF_13', '#skF_11', B_844))), inference(demodulation, [status(thm), theory('equality')], [c_3736, c_790, c_4515, c_11383])).
% 9.03/2.96  tff(c_11889, plain, (![A_18]: (v1_funct_2('#skF_13', '#skF_11', A_18) | ~r2_hidden('#skF_10'('#skF_11', A_18, '#skF_13'), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v5_relat_1('#skF_13', A_18) | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_32, c_11885])).
% 9.03/2.96  tff(c_12148, plain, (![A_847]: (v1_funct_2('#skF_13', '#skF_11', A_847) | ~r2_hidden('#skF_10'('#skF_11', A_847, '#skF_13'), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_3736, c_7732, c_790, c_4515, c_11889])).
% 9.03/2.96  tff(c_12152, plain, (![B_815]: (v1_funct_2('#skF_13', '#skF_11', B_815))), inference(resolution, [status(thm)], [c_10497, c_12148])).
% 9.03/2.96  tff(c_12159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12152, c_3683])).
% 9.03/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.03/2.96  
% 9.03/2.96  Inference rules
% 9.03/2.96  ----------------------
% 9.03/2.96  #Ref     : 0
% 9.03/2.96  #Sup     : 2903
% 9.03/2.96  #Fact    : 0
% 9.03/2.96  #Define  : 0
% 9.03/2.96  #Split   : 25
% 9.03/2.96  #Chain   : 0
% 9.03/2.96  #Close   : 0
% 9.03/2.96  
% 9.03/2.96  Ordering : KBO
% 9.03/2.96  
% 9.03/2.96  Simplification rules
% 9.03/2.96  ----------------------
% 9.03/2.96  #Subsume      : 1076
% 9.03/2.96  #Demod        : 1438
% 9.03/2.96  #Tautology    : 1082
% 9.03/2.96  #SimpNegUnit  : 39
% 9.03/2.96  #BackRed      : 85
% 9.03/2.96  
% 9.03/2.96  #Partial instantiations: 0
% 9.03/2.96  #Strategies tried      : 1
% 9.03/2.96  
% 9.03/2.96  Timing (in seconds)
% 9.03/2.96  ----------------------
% 9.03/2.96  Preprocessing        : 0.41
% 9.03/2.96  Parsing              : 0.21
% 9.03/2.96  CNF conversion       : 0.03
% 9.03/2.96  Main loop            : 1.73
% 9.03/2.96  Inferencing          : 0.59
% 9.03/2.96  Reduction            : 0.57
% 9.03/2.96  Demodulation         : 0.39
% 9.03/2.96  BG Simplification    : 0.06
% 9.03/2.97  Subsumption          : 0.38
% 9.03/2.97  Abstraction          : 0.07
% 9.03/2.97  MUC search           : 0.00
% 9.03/2.97  Cooper               : 0.00
% 9.03/2.97  Total                : 2.19
% 9.03/2.97  Index Insertion      : 0.00
% 9.03/2.97  Index Deletion       : 0.00
% 9.03/2.97  Index Matching       : 0.00
% 9.03/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
