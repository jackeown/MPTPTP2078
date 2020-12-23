%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:36 EST 2020

% Result     : Theorem 9.64s
% Output     : CNFRefutation 9.85s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 217 expanded)
%              Number of leaves         :   45 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  170 ( 517 expanded)
%              Number of equality atoms :   31 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_196,plain,(
    ! [A_83,B_84] :
      ( ~ r2_hidden('#skF_2'(A_83,B_84),B_84)
      | r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_201,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_196])).

tff(c_28,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_165,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_175,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_74,c_165])).

tff(c_180,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_175])).

tff(c_1542,plain,(
    ! [A_248,B_249,C_250,D_251] :
      ( k7_relset_1(A_248,B_249,C_250,D_251) = k9_relat_1(C_250,D_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1565,plain,(
    ! [D_251] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_251) = k9_relat_1('#skF_7',D_251) ),
    inference(resolution,[status(thm)],[c_74,c_1542])).

tff(c_72,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1578,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_72])).

tff(c_961,plain,(
    ! [A_187,B_188,C_189] :
      ( r2_hidden('#skF_3'(A_187,B_188,C_189),B_188)
      | ~ r2_hidden(A_187,k9_relat_1(C_189,B_188))
      | ~ v1_relat_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    ! [F_57] :
      ( k1_funct_1('#skF_7',F_57) != '#skF_8'
      | ~ r2_hidden(F_57,'#skF_6')
      | ~ m1_subset_1(F_57,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_981,plain,(
    ! [A_187,C_189] :
      ( k1_funct_1('#skF_7','#skF_3'(A_187,'#skF_6',C_189)) != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_187,'#skF_6',C_189),'#skF_4')
      | ~ r2_hidden(A_187,k9_relat_1(C_189,'#skF_6'))
      | ~ v1_relat_1(C_189) ) ),
    inference(resolution,[status(thm)],[c_961,c_70])).

tff(c_1605,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_7'),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1578,c_981])).

tff(c_1627,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_7')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_1605])).

tff(c_5024,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1627])).

tff(c_76,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_737,plain,(
    ! [A_163,B_164,C_165] :
      ( k1_relset_1(A_163,B_164,C_165) = k1_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_761,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_737])).

tff(c_2506,plain,(
    ! [B_316,A_317,C_318] :
      ( k1_xboole_0 = B_316
      | k1_relset_1(A_317,B_316,C_318) = A_317
      | ~ v1_funct_2(C_318,A_317,B_316)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_317,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2529,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_2506])).

tff(c_2537,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_761,c_2529])).

tff(c_2538,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2537])).

tff(c_1155,plain,(
    ! [A_210,B_211,C_212] :
      ( r2_hidden('#skF_3'(A_210,B_211,C_212),k1_relat_1(C_212))
      | ~ r2_hidden(A_210,k9_relat_1(C_212,B_211))
      | ~ v1_relat_1(C_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4041,plain,(
    ! [A_433,B_434,C_435] :
      ( m1_subset_1('#skF_3'(A_433,B_434,C_435),k1_relat_1(C_435))
      | ~ r2_hidden(A_433,k9_relat_1(C_435,B_434))
      | ~ v1_relat_1(C_435) ) ),
    inference(resolution,[status(thm)],[c_1155,c_16])).

tff(c_4044,plain,(
    ! [A_433,B_434] :
      ( m1_subset_1('#skF_3'(A_433,B_434,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_433,k9_relat_1('#skF_7',B_434))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2538,c_4041])).

tff(c_10910,plain,(
    ! [A_940,B_941] :
      ( m1_subset_1('#skF_3'(A_940,B_941,'#skF_7'),'#skF_4')
      | ~ r2_hidden(A_940,k9_relat_1('#skF_7',B_941)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_4044])).

tff(c_10965,plain,(
    m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1578,c_10910])).

tff(c_11004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5024,c_10965])).

tff(c_11005,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_7')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1627])).

tff(c_78,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1653,plain,(
    ! [A_255,B_256,C_257] :
      ( r2_hidden(k4_tarski('#skF_3'(A_255,B_256,C_257),A_255),C_257)
      | ~ r2_hidden(A_255,k9_relat_1(C_257,B_256))
      | ~ v1_relat_1(C_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ! [C_37,A_35,B_36] :
      ( k1_funct_1(C_37,A_35) = B_36
      | ~ r2_hidden(k4_tarski(A_35,B_36),C_37)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_11938,plain,(
    ! [C_989,A_990,B_991] :
      ( k1_funct_1(C_989,'#skF_3'(A_990,B_991,C_989)) = A_990
      | ~ v1_funct_1(C_989)
      | ~ r2_hidden(A_990,k9_relat_1(C_989,B_991))
      | ~ v1_relat_1(C_989) ) ),
    inference(resolution,[status(thm)],[c_1653,c_44])).

tff(c_11960,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_7')) = '#skF_8'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1578,c_11938])).

tff(c_11985,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_78,c_11960])).

tff(c_11987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11005,c_11985])).

tff(c_11988,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2537])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_331,plain,(
    ! [C_106,B_107,A_108] :
      ( v5_relat_1(C_106,B_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_350,plain,(
    v5_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_331])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k2_relat_1(B_23),A_22)
      | ~ v5_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [B_33,C_34,A_32] :
      ( r2_hidden(B_33,k2_relat_1(C_34))
      | ~ r2_hidden(k4_tarski(A_32,B_33),C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2169,plain,(
    ! [A_300,C_301,B_302] :
      ( r2_hidden(A_300,k2_relat_1(C_301))
      | ~ r2_hidden(A_300,k9_relat_1(C_301,B_302))
      | ~ v1_relat_1(C_301) ) ),
    inference(resolution,[status(thm)],[c_1653,c_38])).

tff(c_2180,plain,
    ( r2_hidden('#skF_8',k2_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1578,c_2169])).

tff(c_2205,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_2180])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2286,plain,(
    ! [B_307] :
      ( r2_hidden('#skF_8',B_307)
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_307) ) ),
    inference(resolution,[status(thm)],[c_2205,c_6])).

tff(c_2290,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_8',A_22)
      | ~ v5_relat_1('#skF_7',A_22)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_2286])).

tff(c_2305,plain,(
    ! [A_308] :
      ( r2_hidden('#skF_8',A_308)
      | ~ v5_relat_1('#skF_7',A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_2290])).

tff(c_2318,plain,(
    r2_hidden('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_350,c_2305])).

tff(c_2375,plain,(
    ! [B_312] :
      ( r2_hidden('#skF_8',B_312)
      | ~ r1_tarski('#skF_5',B_312) ) ),
    inference(resolution,[status(thm)],[c_2318,c_6])).

tff(c_48,plain,(
    ! [B_39,A_38] :
      ( ~ r1_tarski(B_39,A_38)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2445,plain,(
    ! [B_314] :
      ( ~ r1_tarski(B_314,'#skF_8')
      | ~ r1_tarski('#skF_5',B_314) ) ),
    inference(resolution,[status(thm)],[c_2375,c_48])).

tff(c_2489,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_2445])).

tff(c_11991,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11988,c_2489])).

tff(c_12024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_11991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.64/3.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.64/3.62  
% 9.64/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.64/3.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_2
% 9.64/3.62  
% 9.64/3.62  %Foreground sorts:
% 9.64/3.62  
% 9.64/3.62  
% 9.64/3.62  %Background operators:
% 9.64/3.62  
% 9.64/3.62  
% 9.64/3.62  %Foreground operators:
% 9.64/3.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.64/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.64/3.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.64/3.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.64/3.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.64/3.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.64/3.62  tff('#skF_7', type, '#skF_7': $i).
% 9.64/3.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.64/3.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.64/3.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.64/3.62  tff('#skF_5', type, '#skF_5': $i).
% 9.64/3.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.64/3.62  tff('#skF_6', type, '#skF_6': $i).
% 9.64/3.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.64/3.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.64/3.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.64/3.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.64/3.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.64/3.62  tff('#skF_8', type, '#skF_8': $i).
% 9.64/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.64/3.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.64/3.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.64/3.62  tff('#skF_4', type, '#skF_4': $i).
% 9.64/3.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.64/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.64/3.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.64/3.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.64/3.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.64/3.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.64/3.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.64/3.62  
% 9.85/3.64  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.85/3.64  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.85/3.64  tff(f_155, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 9.85/3.64  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.85/3.64  tff(f_118, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.85/3.64  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 9.85/3.64  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.85/3.64  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.85/3.64  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 9.85/3.64  tff(f_99, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 9.85/3.64  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.85/3.64  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.85/3.64  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.85/3.64  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 9.85/3.64  tff(f_104, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.85/3.64  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.85/3.64  tff(c_196, plain, (![A_83, B_84]: (~r2_hidden('#skF_2'(A_83, B_84), B_84) | r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.85/3.64  tff(c_201, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_196])).
% 9.85/3.64  tff(c_28, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.85/3.64  tff(c_74, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.85/3.64  tff(c_165, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.85/3.64  tff(c_175, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_165])).
% 9.85/3.64  tff(c_180, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_175])).
% 9.85/3.64  tff(c_1542, plain, (![A_248, B_249, C_250, D_251]: (k7_relset_1(A_248, B_249, C_250, D_251)=k9_relat_1(C_250, D_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.85/3.64  tff(c_1565, plain, (![D_251]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_251)=k9_relat_1('#skF_7', D_251))), inference(resolution, [status(thm)], [c_74, c_1542])).
% 9.85/3.64  tff(c_72, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.85/3.64  tff(c_1578, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1565, c_72])).
% 9.85/3.64  tff(c_961, plain, (![A_187, B_188, C_189]: (r2_hidden('#skF_3'(A_187, B_188, C_189), B_188) | ~r2_hidden(A_187, k9_relat_1(C_189, B_188)) | ~v1_relat_1(C_189))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.85/3.64  tff(c_70, plain, (![F_57]: (k1_funct_1('#skF_7', F_57)!='#skF_8' | ~r2_hidden(F_57, '#skF_6') | ~m1_subset_1(F_57, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.85/3.64  tff(c_981, plain, (![A_187, C_189]: (k1_funct_1('#skF_7', '#skF_3'(A_187, '#skF_6', C_189))!='#skF_8' | ~m1_subset_1('#skF_3'(A_187, '#skF_6', C_189), '#skF_4') | ~r2_hidden(A_187, k9_relat_1(C_189, '#skF_6')) | ~v1_relat_1(C_189))), inference(resolution, [status(thm)], [c_961, c_70])).
% 9.85/3.64  tff(c_1605, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_7'), '#skF_4') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1578, c_981])).
% 9.85/3.64  tff(c_1627, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_1605])).
% 9.85/3.64  tff(c_5024, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1627])).
% 9.85/3.64  tff(c_76, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.85/3.64  tff(c_737, plain, (![A_163, B_164, C_165]: (k1_relset_1(A_163, B_164, C_165)=k1_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.85/3.64  tff(c_761, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_74, c_737])).
% 9.85/3.64  tff(c_2506, plain, (![B_316, A_317, C_318]: (k1_xboole_0=B_316 | k1_relset_1(A_317, B_316, C_318)=A_317 | ~v1_funct_2(C_318, A_317, B_316) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_317, B_316))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.85/3.64  tff(c_2529, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_2506])).
% 9.85/3.64  tff(c_2537, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_761, c_2529])).
% 9.85/3.64  tff(c_2538, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_2537])).
% 9.85/3.64  tff(c_1155, plain, (![A_210, B_211, C_212]: (r2_hidden('#skF_3'(A_210, B_211, C_212), k1_relat_1(C_212)) | ~r2_hidden(A_210, k9_relat_1(C_212, B_211)) | ~v1_relat_1(C_212))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.85/3.64  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.85/3.64  tff(c_4041, plain, (![A_433, B_434, C_435]: (m1_subset_1('#skF_3'(A_433, B_434, C_435), k1_relat_1(C_435)) | ~r2_hidden(A_433, k9_relat_1(C_435, B_434)) | ~v1_relat_1(C_435))), inference(resolution, [status(thm)], [c_1155, c_16])).
% 9.85/3.64  tff(c_4044, plain, (![A_433, B_434]: (m1_subset_1('#skF_3'(A_433, B_434, '#skF_7'), '#skF_4') | ~r2_hidden(A_433, k9_relat_1('#skF_7', B_434)) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2538, c_4041])).
% 9.85/3.64  tff(c_10910, plain, (![A_940, B_941]: (m1_subset_1('#skF_3'(A_940, B_941, '#skF_7'), '#skF_4') | ~r2_hidden(A_940, k9_relat_1('#skF_7', B_941)))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_4044])).
% 9.85/3.64  tff(c_10965, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_1578, c_10910])).
% 9.85/3.64  tff(c_11004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5024, c_10965])).
% 9.85/3.64  tff(c_11005, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_7'))!='#skF_8'), inference(splitRight, [status(thm)], [c_1627])).
% 9.85/3.64  tff(c_78, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_155])).
% 9.85/3.64  tff(c_1653, plain, (![A_255, B_256, C_257]: (r2_hidden(k4_tarski('#skF_3'(A_255, B_256, C_257), A_255), C_257) | ~r2_hidden(A_255, k9_relat_1(C_257, B_256)) | ~v1_relat_1(C_257))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.85/3.64  tff(c_44, plain, (![C_37, A_35, B_36]: (k1_funct_1(C_37, A_35)=B_36 | ~r2_hidden(k4_tarski(A_35, B_36), C_37) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.85/3.64  tff(c_11938, plain, (![C_989, A_990, B_991]: (k1_funct_1(C_989, '#skF_3'(A_990, B_991, C_989))=A_990 | ~v1_funct_1(C_989) | ~r2_hidden(A_990, k9_relat_1(C_989, B_991)) | ~v1_relat_1(C_989))), inference(resolution, [status(thm)], [c_1653, c_44])).
% 9.85/3.64  tff(c_11960, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_7'))='#skF_8' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1578, c_11938])).
% 9.85/3.64  tff(c_11985, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_78, c_11960])).
% 9.85/3.64  tff(c_11987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11005, c_11985])).
% 9.85/3.64  tff(c_11988, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2537])).
% 9.85/3.64  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.85/3.64  tff(c_331, plain, (![C_106, B_107, A_108]: (v5_relat_1(C_106, B_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.85/3.64  tff(c_350, plain, (v5_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_331])).
% 9.85/3.64  tff(c_26, plain, (![B_23, A_22]: (r1_tarski(k2_relat_1(B_23), A_22) | ~v5_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.85/3.64  tff(c_38, plain, (![B_33, C_34, A_32]: (r2_hidden(B_33, k2_relat_1(C_34)) | ~r2_hidden(k4_tarski(A_32, B_33), C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.85/3.64  tff(c_2169, plain, (![A_300, C_301, B_302]: (r2_hidden(A_300, k2_relat_1(C_301)) | ~r2_hidden(A_300, k9_relat_1(C_301, B_302)) | ~v1_relat_1(C_301))), inference(resolution, [status(thm)], [c_1653, c_38])).
% 9.85/3.64  tff(c_2180, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1578, c_2169])).
% 9.85/3.64  tff(c_2205, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_2180])).
% 9.85/3.64  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.85/3.64  tff(c_2286, plain, (![B_307]: (r2_hidden('#skF_8', B_307) | ~r1_tarski(k2_relat_1('#skF_7'), B_307))), inference(resolution, [status(thm)], [c_2205, c_6])).
% 9.85/3.64  tff(c_2290, plain, (![A_22]: (r2_hidden('#skF_8', A_22) | ~v5_relat_1('#skF_7', A_22) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_26, c_2286])).
% 9.85/3.64  tff(c_2305, plain, (![A_308]: (r2_hidden('#skF_8', A_308) | ~v5_relat_1('#skF_7', A_308))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_2290])).
% 9.85/3.64  tff(c_2318, plain, (r2_hidden('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_350, c_2305])).
% 9.85/3.64  tff(c_2375, plain, (![B_312]: (r2_hidden('#skF_8', B_312) | ~r1_tarski('#skF_5', B_312))), inference(resolution, [status(thm)], [c_2318, c_6])).
% 9.85/3.64  tff(c_48, plain, (![B_39, A_38]: (~r1_tarski(B_39, A_38) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.85/3.64  tff(c_2445, plain, (![B_314]: (~r1_tarski(B_314, '#skF_8') | ~r1_tarski('#skF_5', B_314))), inference(resolution, [status(thm)], [c_2375, c_48])).
% 9.85/3.64  tff(c_2489, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_2445])).
% 9.85/3.64  tff(c_11991, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11988, c_2489])).
% 9.85/3.64  tff(c_12024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_201, c_11991])).
% 9.85/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.85/3.64  
% 9.85/3.64  Inference rules
% 9.85/3.64  ----------------------
% 9.85/3.64  #Ref     : 0
% 9.85/3.64  #Sup     : 2397
% 9.85/3.64  #Fact    : 0
% 9.85/3.64  #Define  : 0
% 9.85/3.64  #Split   : 21
% 9.85/3.64  #Chain   : 0
% 9.85/3.64  #Close   : 0
% 9.85/3.64  
% 9.85/3.64  Ordering : KBO
% 9.85/3.64  
% 9.85/3.64  Simplification rules
% 9.85/3.64  ----------------------
% 9.85/3.64  #Subsume      : 412
% 9.85/3.64  #Demod        : 764
% 9.85/3.64  #Tautology    : 311
% 9.85/3.64  #SimpNegUnit  : 19
% 9.85/3.64  #BackRed      : 45
% 9.85/3.64  
% 9.85/3.64  #Partial instantiations: 0
% 9.85/3.64  #Strategies tried      : 1
% 9.85/3.64  
% 9.85/3.64  Timing (in seconds)
% 9.85/3.64  ----------------------
% 9.85/3.64  Preprocessing        : 0.35
% 9.85/3.64  Parsing              : 0.18
% 9.85/3.64  CNF conversion       : 0.03
% 9.85/3.64  Main loop            : 2.53
% 9.85/3.64  Inferencing          : 0.78
% 9.85/3.64  Reduction            : 0.89
% 9.85/3.64  Demodulation         : 0.65
% 9.85/3.64  BG Simplification    : 0.06
% 9.85/3.64  Subsumption          : 0.58
% 9.85/3.64  Abstraction          : 0.10
% 9.85/3.64  MUC search           : 0.00
% 9.85/3.64  Cooper               : 0.00
% 9.85/3.64  Total                : 2.91
% 9.85/3.64  Index Insertion      : 0.00
% 9.85/3.64  Index Deletion       : 0.00
% 9.85/3.64  Index Matching       : 0.00
% 9.85/3.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
