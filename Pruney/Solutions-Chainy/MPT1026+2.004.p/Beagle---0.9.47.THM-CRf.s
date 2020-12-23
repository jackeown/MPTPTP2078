%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:39 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 422 expanded)
%              Number of leaves         :   46 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          :  273 ( 983 expanded)
%              Number of equality atoms :   42 ( 136 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_160,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_51,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_170,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_105,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_102,plain,(
    r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2965,plain,(
    ! [A_305,B_306,D_307] :
      ( '#skF_7'(A_305,B_306,k1_funct_2(A_305,B_306),D_307) = D_307
      | ~ r2_hidden(D_307,k1_funct_2(A_305,B_306)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2984,plain,(
    '#skF_7'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_102,c_2965])).

tff(c_68,plain,(
    ! [A_48,B_49,D_64] :
      ( v1_relat_1('#skF_7'(A_48,B_49,k1_funct_2(A_48,B_49),D_64))
      | ~ r2_hidden(D_64,k1_funct_2(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2988,plain,
    ( v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2984,c_68])).

tff(c_2992,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2988])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3079,plain,(
    ! [A_316,B_317,D_318] :
      ( k1_relat_1('#skF_7'(A_316,B_317,k1_funct_2(A_316,B_317),D_318)) = A_316
      | ~ r2_hidden(D_318,k1_funct_2(A_316,B_317)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3103,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2984,c_3079])).

tff(c_3107,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_3103])).

tff(c_3254,plain,(
    ! [A_323,B_324,D_325] :
      ( r1_tarski(k2_relat_1('#skF_7'(A_323,B_324,k1_funct_2(A_323,B_324),D_325)),B_324)
      | ~ r2_hidden(D_325,k1_funct_2(A_323,B_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_3285,plain,
    ( r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2984,c_3254])).

tff(c_3296,plain,(
    r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_3285])).

tff(c_4043,plain,(
    ! [C_382,A_383,B_384] :
      ( m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384)))
      | ~ r1_tarski(k2_relat_1(C_382),B_384)
      | ~ r1_tarski(k1_relat_1(C_382),A_383)
      | ~ v1_relat_1(C_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_100,plain,
    ( ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_119,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_1551,plain,(
    ! [A_195,B_196,D_197] :
      ( '#skF_7'(A_195,B_196,k1_funct_2(A_195,B_196),D_197) = D_197
      | ~ r2_hidden(D_197,k1_funct_2(A_195,B_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1570,plain,(
    '#skF_7'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_102,c_1551])).

tff(c_66,plain,(
    ! [A_48,B_49,D_64] :
      ( v1_funct_1('#skF_7'(A_48,B_49,k1_funct_2(A_48,B_49),D_64))
      | ~ r2_hidden(D_64,k1_funct_2(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1577,plain,
    ( v1_funct_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1570,c_66])).

tff(c_1583,plain,(
    v1_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1577])).

tff(c_1585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_1583])).

tff(c_1586,plain,
    ( ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_1623,plain,(
    ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_1586])).

tff(c_4061,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_8')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_4043,c_1623])).

tff(c_4076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2992,c_14,c_3107,c_3296,c_4061])).

tff(c_4077,plain,(
    ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1586])).

tff(c_1587,plain,(
    v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_4078,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_1586])).

tff(c_8797,plain,(
    ! [C_701,A_702,B_703] :
      ( v1_partfun1(C_701,A_702)
      | ~ m1_subset_1(C_701,k1_zfmisc_1(k2_zfmisc_1(A_702,B_703)))
      | ~ v1_xboole_0(A_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8814,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4078,c_8797])).

tff(c_8817,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_8814])).

tff(c_30,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [B_22,A_20] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4081,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_4078,c_28])).

tff(c_4087,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4081])).

tff(c_42,plain,(
    ! [A_31] :
      ( k2_relat_1(A_31) = k1_xboole_0
      | k1_relat_1(A_31) != k1_xboole_0
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4092,plain,
    ( k2_relat_1('#skF_10') = k1_xboole_0
    | k1_relat_1('#skF_10') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4087,c_42])).

tff(c_4098,plain,(
    k1_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4092])).

tff(c_4161,plain,(
    ! [A_394] :
      ( k1_relat_1(A_394) = k1_xboole_0
      | k2_relat_1(A_394) != k1_xboole_0
      | ~ v1_relat_1(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4173,plain,
    ( k1_relat_1('#skF_10') = k1_xboole_0
    | k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4087,c_4161])).

tff(c_4184,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4098,c_4173])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4347,plain,(
    ! [C_412,B_413,A_414] :
      ( ~ v1_xboole_0(C_412)
      | ~ m1_subset_1(B_413,k1_zfmisc_1(C_412))
      | ~ r2_hidden(A_414,B_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4520,plain,(
    ! [B_424,A_425,A_426] :
      ( ~ v1_xboole_0(B_424)
      | ~ r2_hidden(A_425,A_426)
      | ~ r1_tarski(A_426,B_424) ) ),
    inference(resolution,[status(thm)],[c_24,c_4347])).

tff(c_4620,plain,(
    ! [B_433,A_434,B_435] :
      ( ~ v1_xboole_0(B_433)
      | ~ r1_tarski(A_434,B_433)
      | r1_tarski(A_434,B_435) ) ),
    inference(resolution,[status(thm)],[c_6,c_4520])).

tff(c_4640,plain,(
    ! [B_9,B_435] :
      ( ~ v1_xboole_0(B_9)
      | r1_tarski(B_9,B_435) ) ),
    inference(resolution,[status(thm)],[c_14,c_4620])).

tff(c_5152,plain,(
    ! [A_471,B_472,D_473] :
      ( '#skF_7'(A_471,B_472,k1_funct_2(A_471,B_472),D_473) = D_473
      | ~ r2_hidden(D_473,k1_funct_2(A_471,B_472)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5171,plain,(
    '#skF_7'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_102,c_5152])).

tff(c_5594,plain,(
    ! [A_495,B_496,D_497] :
      ( k1_relat_1('#skF_7'(A_495,B_496,k1_funct_2(A_495,B_496),D_497)) = A_495
      | ~ r2_hidden(D_497,k1_funct_2(A_495,B_496)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5618,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5171,c_5594])).

tff(c_5622,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_5618])).

tff(c_5697,plain,(
    ! [E_498,B_499] :
      ( r2_hidden(E_498,k1_funct_2(k1_relat_1(E_498),B_499))
      | ~ r1_tarski(k2_relat_1(E_498),B_499)
      | ~ v1_funct_1(E_498)
      | ~ v1_relat_1(E_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_5712,plain,(
    ! [B_499] :
      ( r2_hidden('#skF_10',k1_funct_2('#skF_8',B_499))
      | ~ r1_tarski(k2_relat_1('#skF_10'),B_499)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5622,c_5697])).

tff(c_5798,plain,(
    ! [B_503] :
      ( r2_hidden('#skF_10',k1_funct_2('#skF_8',B_503))
      | ~ r1_tarski(k2_relat_1('#skF_10'),B_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4087,c_1587,c_5712])).

tff(c_18,plain,(
    ! [A_11] : m1_subset_1('#skF_3'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1596,plain,(
    ! [A_201,B_202] :
      ( r1_tarski(A_201,B_202)
      | ~ m1_subset_1(A_201,k1_zfmisc_1(B_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1605,plain,(
    ! [B_202] : r1_tarski('#skF_3'(k1_zfmisc_1(B_202)),B_202) ),
    inference(resolution,[status(thm)],[c_18,c_1596])).

tff(c_4643,plain,(
    ! [B_436,B_437] :
      ( ~ v1_xboole_0(B_436)
      | r1_tarski(B_436,B_437) ) ),
    inference(resolution,[status(thm)],[c_14,c_4620])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4736,plain,(
    ! [B_443,B_442] :
      ( B_443 = B_442
      | ~ r1_tarski(B_442,B_443)
      | ~ v1_xboole_0(B_443) ) ),
    inference(resolution,[status(thm)],[c_4643,c_10])).

tff(c_4795,plain,(
    ! [B_449] :
      ( '#skF_3'(k1_zfmisc_1(B_449)) = B_449
      | ~ v1_xboole_0(B_449) ) ),
    inference(resolution,[status(thm)],[c_1605,c_4736])).

tff(c_4836,plain,(
    ! [B_450] :
      ( m1_subset_1(B_450,k1_zfmisc_1(B_450))
      | ~ v1_xboole_0(B_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4795,c_18])).

tff(c_26,plain,(
    ! [C_19,B_18,A_17] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4850,plain,(
    ! [A_17,B_450] :
      ( ~ r2_hidden(A_17,B_450)
      | ~ v1_xboole_0(B_450) ) ),
    inference(resolution,[status(thm)],[c_4836,c_26])).

tff(c_5816,plain,(
    ! [B_504] :
      ( ~ v1_xboole_0(k1_funct_2('#skF_8',B_504))
      | ~ r1_tarski(k2_relat_1('#skF_10'),B_504) ) ),
    inference(resolution,[status(thm)],[c_5798,c_4850])).

tff(c_5836,plain,(
    ! [B_435] :
      ( ~ v1_xboole_0(k1_funct_2('#skF_8',B_435))
      | ~ v1_xboole_0(k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_4640,c_5816])).

tff(c_5839,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_5836])).

tff(c_6008,plain,(
    ! [C_520,A_521,B_522] :
      ( v1_funct_2(C_520,A_521,B_522)
      | ~ v1_partfun1(C_520,A_521)
      | ~ v1_funct_1(C_520)
      | ~ m1_subset_1(C_520,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6025,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_4078,c_6008])).

tff(c_6042,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_6025])).

tff(c_6043,plain,(
    ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_4077,c_6042])).

tff(c_96,plain,(
    ! [A_68] :
      ( v1_funct_2(A_68,k1_relat_1(A_68),k2_relat_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_5636,plain,
    ( v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_5622,c_96])).

tff(c_5649,plain,(
    v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4087,c_1587,c_5636])).

tff(c_94,plain,(
    ! [A_68] :
      ( m1_subset_1(A_68,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_68),k2_relat_1(A_68))))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_5627,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_5622,c_94])).

tff(c_5643,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4087,c_1587,c_5627])).

tff(c_7104,plain,(
    ! [C_587,A_588,B_589] :
      ( v1_partfun1(C_587,A_588)
      | ~ v1_funct_2(C_587,A_588,B_589)
      | ~ v1_funct_1(C_587)
      | ~ m1_subset_1(C_587,k1_zfmisc_1(k2_zfmisc_1(A_588,B_589)))
      | v1_xboole_0(B_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_7110,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_5643,c_7104])).

tff(c_7136,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_5649,c_7110])).

tff(c_7138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5839,c_6043,c_7136])).

tff(c_7140,plain,(
    v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_5836])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4533,plain,(
    ! [B_427,A_428] :
      ( ~ v1_xboole_0(B_427)
      | ~ r1_tarski(A_428,B_427)
      | k1_xboole_0 = A_428 ) ),
    inference(resolution,[status(thm)],[c_8,c_4520])).

tff(c_4560,plain,(
    ! [B_9] :
      ( ~ v1_xboole_0(B_9)
      | k1_xboole_0 = B_9 ) ),
    inference(resolution,[status(thm)],[c_14,c_4533])).

tff(c_7150,plain,(
    k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7140,c_4560])).

tff(c_7157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4184,c_7150])).

tff(c_7159,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4092])).

tff(c_10483,plain,(
    ! [A_777,B_778,D_779] :
      ( '#skF_7'(A_777,B_778,k1_funct_2(A_777,B_778),D_779) = D_779
      | ~ r2_hidden(D_779,k1_funct_2(A_777,B_778)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10502,plain,(
    '#skF_7'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_102,c_10483])).

tff(c_10692,plain,(
    ! [A_784,B_785,D_786] :
      ( k1_relat_1('#skF_7'(A_784,B_785,k1_funct_2(A_784,B_785),D_786)) = A_784
      | ~ r2_hidden(D_786,k1_funct_2(A_784,B_785)) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10725,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10502,c_10692])).

tff(c_10729,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_7159,c_10725])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8390,plain,(
    ! [A_666,B_667] :
      ( r2_hidden(A_666,B_667)
      | v1_xboole_0(B_667)
      | ~ m1_subset_1(A_666,B_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [B_33,A_32] :
      ( ~ r1_tarski(B_33,A_32)
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8491,plain,(
    ! [B_674,A_675] :
      ( ~ r1_tarski(B_674,A_675)
      | v1_xboole_0(B_674)
      | ~ m1_subset_1(A_675,B_674) ) ),
    inference(resolution,[status(thm)],[c_8390,c_44])).

tff(c_8519,plain,(
    ! [A_10] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_8491])).

tff(c_8541,plain,(
    ! [A_680] : ~ m1_subset_1(A_680,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8519])).

tff(c_8546,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_8541])).

tff(c_8547,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8519])).

tff(c_10762,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10729,c_8547])).

tff(c_10779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8817,c_10762])).

tff(c_10780,plain,(
    v1_partfun1('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_8814])).

tff(c_12143,plain,(
    ! [C_855,A_856,B_857] :
      ( v1_funct_2(C_855,A_856,B_857)
      | ~ v1_partfun1(C_855,A_856)
      | ~ v1_funct_1(C_855)
      | ~ m1_subset_1(C_855,k1_zfmisc_1(k2_zfmisc_1(A_856,B_857))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12160,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_4078,c_12143])).

tff(c_12177,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_10780,c_12160])).

tff(c_12179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4077,c_12177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:53:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.56/2.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.79  
% 7.56/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.79  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 7.56/2.79  
% 7.56/2.79  %Foreground sorts:
% 7.56/2.79  
% 7.56/2.79  
% 7.56/2.79  %Background operators:
% 7.56/2.79  
% 7.56/2.79  
% 7.56/2.79  %Foreground operators:
% 7.56/2.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.56/2.79  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.56/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.56/2.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.56/2.79  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.56/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.56/2.79  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.56/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.56/2.79  tff('#skF_10', type, '#skF_10': $i).
% 7.56/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.56/2.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.56/2.79  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.56/2.79  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.56/2.79  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 7.56/2.79  tff('#skF_9', type, '#skF_9': $i).
% 7.56/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.56/2.79  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 7.56/2.79  tff('#skF_8', type, '#skF_8': $i).
% 7.56/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.56/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.56/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.56/2.79  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.56/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.56/2.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.56/2.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.56/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.56/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.56/2.79  
% 7.91/2.82  tff(f_179, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 7.91/2.82  tff(f_160, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 7.91/2.82  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.91/2.82  tff(f_113, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 7.91/2.82  tff(f_130, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 7.91/2.82  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.91/2.82  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.91/2.82  tff(f_100, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 7.91/2.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.91/2.82  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.91/2.82  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.91/2.82  tff(f_51, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 7.91/2.82  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.91/2.82  tff(f_170, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.91/2.82  tff(f_144, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.91/2.82  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.91/2.82  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.91/2.82  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.91/2.82  tff(f_105, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.91/2.82  tff(c_102, plain, (r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.91/2.82  tff(c_2965, plain, (![A_305, B_306, D_307]: ('#skF_7'(A_305, B_306, k1_funct_2(A_305, B_306), D_307)=D_307 | ~r2_hidden(D_307, k1_funct_2(A_305, B_306)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_2984, plain, ('#skF_7'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_102, c_2965])).
% 7.91/2.82  tff(c_68, plain, (![A_48, B_49, D_64]: (v1_relat_1('#skF_7'(A_48, B_49, k1_funct_2(A_48, B_49), D_64)) | ~r2_hidden(D_64, k1_funct_2(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_2988, plain, (v1_relat_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2984, c_68])).
% 7.91/2.82  tff(c_2992, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2988])).
% 7.91/2.82  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.91/2.82  tff(c_3079, plain, (![A_316, B_317, D_318]: (k1_relat_1('#skF_7'(A_316, B_317, k1_funct_2(A_316, B_317), D_318))=A_316 | ~r2_hidden(D_318, k1_funct_2(A_316, B_317)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_3103, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2984, c_3079])).
% 7.91/2.82  tff(c_3107, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_3103])).
% 7.91/2.82  tff(c_3254, plain, (![A_323, B_324, D_325]: (r1_tarski(k2_relat_1('#skF_7'(A_323, B_324, k1_funct_2(A_323, B_324), D_325)), B_324) | ~r2_hidden(D_325, k1_funct_2(A_323, B_324)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_3285, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2984, c_3254])).
% 7.91/2.82  tff(c_3296, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_3285])).
% 7.91/2.82  tff(c_4043, plain, (![C_382, A_383, B_384]: (m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))) | ~r1_tarski(k2_relat_1(C_382), B_384) | ~r1_tarski(k1_relat_1(C_382), A_383) | ~v1_relat_1(C_382))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.91/2.82  tff(c_100, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.91/2.82  tff(c_119, plain, (~v1_funct_1('#skF_10')), inference(splitLeft, [status(thm)], [c_100])).
% 7.91/2.82  tff(c_1551, plain, (![A_195, B_196, D_197]: ('#skF_7'(A_195, B_196, k1_funct_2(A_195, B_196), D_197)=D_197 | ~r2_hidden(D_197, k1_funct_2(A_195, B_196)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_1570, plain, ('#skF_7'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_102, c_1551])).
% 7.91/2.82  tff(c_66, plain, (![A_48, B_49, D_64]: (v1_funct_1('#skF_7'(A_48, B_49, k1_funct_2(A_48, B_49), D_64)) | ~r2_hidden(D_64, k1_funct_2(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_1577, plain, (v1_funct_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1570, c_66])).
% 7.91/2.82  tff(c_1583, plain, (v1_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1577])).
% 7.91/2.82  tff(c_1585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_1583])).
% 7.91/2.82  tff(c_1586, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_100])).
% 7.91/2.82  tff(c_1623, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitLeft, [status(thm)], [c_1586])).
% 7.91/2.82  tff(c_4061, plain, (~r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_8') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_4043, c_1623])).
% 7.91/2.82  tff(c_4076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2992, c_14, c_3107, c_3296, c_4061])).
% 7.91/2.82  tff(c_4077, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_1586])).
% 7.91/2.82  tff(c_1587, plain, (v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_100])).
% 7.91/2.82  tff(c_4078, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_1586])).
% 7.91/2.82  tff(c_8797, plain, (![C_701, A_702, B_703]: (v1_partfun1(C_701, A_702) | ~m1_subset_1(C_701, k1_zfmisc_1(k2_zfmisc_1(A_702, B_703))) | ~v1_xboole_0(A_702))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.91/2.82  tff(c_8814, plain, (v1_partfun1('#skF_10', '#skF_8') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4078, c_8797])).
% 7.91/2.82  tff(c_8817, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_8814])).
% 7.91/2.82  tff(c_30, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.91/2.82  tff(c_28, plain, (![B_22, A_20]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.91/2.82  tff(c_4081, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_4078, c_28])).
% 7.91/2.82  tff(c_4087, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4081])).
% 7.91/2.82  tff(c_42, plain, (![A_31]: (k2_relat_1(A_31)=k1_xboole_0 | k1_relat_1(A_31)!=k1_xboole_0 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.91/2.82  tff(c_4092, plain, (k2_relat_1('#skF_10')=k1_xboole_0 | k1_relat_1('#skF_10')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4087, c_42])).
% 7.91/2.82  tff(c_4098, plain, (k1_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4092])).
% 7.91/2.82  tff(c_4161, plain, (![A_394]: (k1_relat_1(A_394)=k1_xboole_0 | k2_relat_1(A_394)!=k1_xboole_0 | ~v1_relat_1(A_394))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.91/2.82  tff(c_4173, plain, (k1_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4087, c_4161])).
% 7.91/2.82  tff(c_4184, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4098, c_4173])).
% 7.91/2.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.91/2.82  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.91/2.82  tff(c_4347, plain, (![C_412, B_413, A_414]: (~v1_xboole_0(C_412) | ~m1_subset_1(B_413, k1_zfmisc_1(C_412)) | ~r2_hidden(A_414, B_413))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.91/2.82  tff(c_4520, plain, (![B_424, A_425, A_426]: (~v1_xboole_0(B_424) | ~r2_hidden(A_425, A_426) | ~r1_tarski(A_426, B_424))), inference(resolution, [status(thm)], [c_24, c_4347])).
% 7.91/2.82  tff(c_4620, plain, (![B_433, A_434, B_435]: (~v1_xboole_0(B_433) | ~r1_tarski(A_434, B_433) | r1_tarski(A_434, B_435))), inference(resolution, [status(thm)], [c_6, c_4520])).
% 7.91/2.82  tff(c_4640, plain, (![B_9, B_435]: (~v1_xboole_0(B_9) | r1_tarski(B_9, B_435))), inference(resolution, [status(thm)], [c_14, c_4620])).
% 7.91/2.82  tff(c_5152, plain, (![A_471, B_472, D_473]: ('#skF_7'(A_471, B_472, k1_funct_2(A_471, B_472), D_473)=D_473 | ~r2_hidden(D_473, k1_funct_2(A_471, B_472)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_5171, plain, ('#skF_7'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_102, c_5152])).
% 7.91/2.82  tff(c_5594, plain, (![A_495, B_496, D_497]: (k1_relat_1('#skF_7'(A_495, B_496, k1_funct_2(A_495, B_496), D_497))=A_495 | ~r2_hidden(D_497, k1_funct_2(A_495, B_496)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_5618, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5171, c_5594])).
% 7.91/2.82  tff(c_5622, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_5618])).
% 7.91/2.82  tff(c_5697, plain, (![E_498, B_499]: (r2_hidden(E_498, k1_funct_2(k1_relat_1(E_498), B_499)) | ~r1_tarski(k2_relat_1(E_498), B_499) | ~v1_funct_1(E_498) | ~v1_relat_1(E_498))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_5712, plain, (![B_499]: (r2_hidden('#skF_10', k1_funct_2('#skF_8', B_499)) | ~r1_tarski(k2_relat_1('#skF_10'), B_499) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5622, c_5697])).
% 7.91/2.82  tff(c_5798, plain, (![B_503]: (r2_hidden('#skF_10', k1_funct_2('#skF_8', B_503)) | ~r1_tarski(k2_relat_1('#skF_10'), B_503))), inference(demodulation, [status(thm), theory('equality')], [c_4087, c_1587, c_5712])).
% 7.91/2.82  tff(c_18, plain, (![A_11]: (m1_subset_1('#skF_3'(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.91/2.82  tff(c_1596, plain, (![A_201, B_202]: (r1_tarski(A_201, B_202) | ~m1_subset_1(A_201, k1_zfmisc_1(B_202)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.91/2.82  tff(c_1605, plain, (![B_202]: (r1_tarski('#skF_3'(k1_zfmisc_1(B_202)), B_202))), inference(resolution, [status(thm)], [c_18, c_1596])).
% 7.91/2.82  tff(c_4643, plain, (![B_436, B_437]: (~v1_xboole_0(B_436) | r1_tarski(B_436, B_437))), inference(resolution, [status(thm)], [c_14, c_4620])).
% 7.91/2.82  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.91/2.82  tff(c_4736, plain, (![B_443, B_442]: (B_443=B_442 | ~r1_tarski(B_442, B_443) | ~v1_xboole_0(B_443))), inference(resolution, [status(thm)], [c_4643, c_10])).
% 7.91/2.82  tff(c_4795, plain, (![B_449]: ('#skF_3'(k1_zfmisc_1(B_449))=B_449 | ~v1_xboole_0(B_449))), inference(resolution, [status(thm)], [c_1605, c_4736])).
% 7.91/2.82  tff(c_4836, plain, (![B_450]: (m1_subset_1(B_450, k1_zfmisc_1(B_450)) | ~v1_xboole_0(B_450))), inference(superposition, [status(thm), theory('equality')], [c_4795, c_18])).
% 7.91/2.82  tff(c_26, plain, (![C_19, B_18, A_17]: (~v1_xboole_0(C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(C_19)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.91/2.82  tff(c_4850, plain, (![A_17, B_450]: (~r2_hidden(A_17, B_450) | ~v1_xboole_0(B_450))), inference(resolution, [status(thm)], [c_4836, c_26])).
% 7.91/2.82  tff(c_5816, plain, (![B_504]: (~v1_xboole_0(k1_funct_2('#skF_8', B_504)) | ~r1_tarski(k2_relat_1('#skF_10'), B_504))), inference(resolution, [status(thm)], [c_5798, c_4850])).
% 7.91/2.82  tff(c_5836, plain, (![B_435]: (~v1_xboole_0(k1_funct_2('#skF_8', B_435)) | ~v1_xboole_0(k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_4640, c_5816])).
% 7.91/2.82  tff(c_5839, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_5836])).
% 7.91/2.82  tff(c_6008, plain, (![C_520, A_521, B_522]: (v1_funct_2(C_520, A_521, B_522) | ~v1_partfun1(C_520, A_521) | ~v1_funct_1(C_520) | ~m1_subset_1(C_520, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.91/2.82  tff(c_6025, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_4078, c_6008])).
% 7.91/2.82  tff(c_6042, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_6025])).
% 7.91/2.82  tff(c_6043, plain, (~v1_partfun1('#skF_10', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_4077, c_6042])).
% 7.91/2.82  tff(c_96, plain, (![A_68]: (v1_funct_2(A_68, k1_relat_1(A_68), k2_relat_1(A_68)) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.91/2.82  tff(c_5636, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_5622, c_96])).
% 7.91/2.82  tff(c_5649, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_4087, c_1587, c_5636])).
% 7.91/2.82  tff(c_94, plain, (![A_68]: (m1_subset_1(A_68, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_68), k2_relat_1(A_68)))) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.91/2.82  tff(c_5627, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_5622, c_94])).
% 7.91/2.82  tff(c_5643, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_4087, c_1587, c_5627])).
% 7.91/2.82  tff(c_7104, plain, (![C_587, A_588, B_589]: (v1_partfun1(C_587, A_588) | ~v1_funct_2(C_587, A_588, B_589) | ~v1_funct_1(C_587) | ~m1_subset_1(C_587, k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))) | v1_xboole_0(B_589))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.91/2.82  tff(c_7110, plain, (v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_5643, c_7104])).
% 7.91/2.82  tff(c_7136, plain, (v1_partfun1('#skF_10', '#skF_8') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_5649, c_7110])).
% 7.91/2.82  tff(c_7138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5839, c_6043, c_7136])).
% 7.91/2.82  tff(c_7140, plain, (v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_5836])).
% 7.91/2.82  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.91/2.82  tff(c_4533, plain, (![B_427, A_428]: (~v1_xboole_0(B_427) | ~r1_tarski(A_428, B_427) | k1_xboole_0=A_428)), inference(resolution, [status(thm)], [c_8, c_4520])).
% 7.91/2.82  tff(c_4560, plain, (![B_9]: (~v1_xboole_0(B_9) | k1_xboole_0=B_9)), inference(resolution, [status(thm)], [c_14, c_4533])).
% 7.91/2.82  tff(c_7150, plain, (k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_7140, c_4560])).
% 7.91/2.82  tff(c_7157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4184, c_7150])).
% 7.91/2.82  tff(c_7159, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4092])).
% 7.91/2.82  tff(c_10483, plain, (![A_777, B_778, D_779]: ('#skF_7'(A_777, B_778, k1_funct_2(A_777, B_778), D_779)=D_779 | ~r2_hidden(D_779, k1_funct_2(A_777, B_778)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_10502, plain, ('#skF_7'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_102, c_10483])).
% 7.91/2.82  tff(c_10692, plain, (![A_784, B_785, D_786]: (k1_relat_1('#skF_7'(A_784, B_785, k1_funct_2(A_784, B_785), D_786))=A_784 | ~r2_hidden(D_786, k1_funct_2(A_784, B_785)))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.91/2.82  tff(c_10725, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10502, c_10692])).
% 7.91/2.82  tff(c_10729, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_7159, c_10725])).
% 7.91/2.82  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.91/2.82  tff(c_8390, plain, (![A_666, B_667]: (r2_hidden(A_666, B_667) | v1_xboole_0(B_667) | ~m1_subset_1(A_666, B_667))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.91/2.82  tff(c_44, plain, (![B_33, A_32]: (~r1_tarski(B_33, A_32) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.91/2.82  tff(c_8491, plain, (![B_674, A_675]: (~r1_tarski(B_674, A_675) | v1_xboole_0(B_674) | ~m1_subset_1(A_675, B_674))), inference(resolution, [status(thm)], [c_8390, c_44])).
% 7.91/2.82  tff(c_8519, plain, (![A_10]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_8491])).
% 7.91/2.82  tff(c_8541, plain, (![A_680]: (~m1_subset_1(A_680, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8519])).
% 7.91/2.82  tff(c_8546, plain, $false, inference(resolution, [status(thm)], [c_18, c_8541])).
% 7.91/2.82  tff(c_8547, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_8519])).
% 7.91/2.82  tff(c_10762, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10729, c_8547])).
% 7.91/2.82  tff(c_10779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8817, c_10762])).
% 7.91/2.82  tff(c_10780, plain, (v1_partfun1('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_8814])).
% 7.91/2.82  tff(c_12143, plain, (![C_855, A_856, B_857]: (v1_funct_2(C_855, A_856, B_857) | ~v1_partfun1(C_855, A_856) | ~v1_funct_1(C_855) | ~m1_subset_1(C_855, k1_zfmisc_1(k2_zfmisc_1(A_856, B_857))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.91/2.82  tff(c_12160, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_4078, c_12143])).
% 7.91/2.82  tff(c_12177, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_10780, c_12160])).
% 7.91/2.82  tff(c_12179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4077, c_12177])).
% 7.91/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.82  
% 7.91/2.82  Inference rules
% 7.91/2.82  ----------------------
% 7.91/2.82  #Ref     : 0
% 7.91/2.82  #Sup     : 2635
% 7.91/2.82  #Fact    : 0
% 7.91/2.82  #Define  : 0
% 7.91/2.82  #Split   : 74
% 7.91/2.82  #Chain   : 0
% 7.91/2.82  #Close   : 0
% 7.91/2.82  
% 7.91/2.82  Ordering : KBO
% 7.91/2.82  
% 7.91/2.82  Simplification rules
% 7.91/2.82  ----------------------
% 7.91/2.82  #Subsume      : 872
% 7.91/2.82  #Demod        : 1330
% 7.91/2.82  #Tautology    : 771
% 7.91/2.82  #SimpNegUnit  : 168
% 7.91/2.82  #BackRed      : 140
% 7.91/2.82  
% 7.91/2.82  #Partial instantiations: 0
% 7.91/2.82  #Strategies tried      : 1
% 7.91/2.82  
% 7.91/2.82  Timing (in seconds)
% 7.91/2.82  ----------------------
% 7.91/2.82  Preprocessing        : 0.37
% 7.91/2.82  Parsing              : 0.18
% 7.91/2.82  CNF conversion       : 0.03
% 7.91/2.82  Main loop            : 1.60
% 7.91/2.82  Inferencing          : 0.53
% 7.91/2.82  Reduction            : 0.50
% 7.91/2.82  Demodulation         : 0.33
% 7.91/2.82  BG Simplification    : 0.06
% 7.91/2.82  Subsumption          : 0.36
% 7.91/2.82  Abstraction          : 0.07
% 7.91/2.82  MUC search           : 0.00
% 7.91/2.82  Cooper               : 0.00
% 7.91/2.82  Total                : 2.02
% 7.91/2.82  Index Insertion      : 0.00
% 7.91/2.82  Index Deletion       : 0.00
% 7.91/2.82  Index Matching       : 0.00
% 7.91/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
