%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:52 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 291 expanded)
%              Number of leaves         :   36 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 (1152 expanded)
%              Number of equality atoms :   26 ( 281 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_226,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_166,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_183,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_203,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_82,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_1212,plain,(
    ! [B_185,C_186,A_187] :
      ( k1_xboole_0 = B_185
      | v1_partfun1(C_186,A_187)
      | ~ v1_funct_2(C_186,A_187,B_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_185)))
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1218,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_1212])).

tff(c_1225,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_1218])).

tff(c_1226,plain,(
    v1_partfun1('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1225])).

tff(c_78,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_76,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_74,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_1215,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_partfun1('#skF_7','#skF_4')
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_1212])).

tff(c_1221,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_partfun1('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1215])).

tff(c_1222,plain,(
    v1_partfun1('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1221])).

tff(c_72,plain,(
    r1_partfun1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_1790,plain,(
    ! [D_232,C_233,A_234,B_235] :
      ( D_232 = C_233
      | ~ r1_partfun1(C_233,D_232)
      | ~ v1_partfun1(D_232,A_234)
      | ~ v1_partfun1(C_233,A_234)
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(D_232)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1794,plain,(
    ! [A_234,B_235] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_234)
      | ~ v1_partfun1('#skF_6',A_234)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_1790])).

tff(c_1800,plain,(
    ! [A_234,B_235] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_234)
      | ~ v1_partfun1('#skF_6',A_234)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_78,c_1794])).

tff(c_3100,plain,(
    ! [A_334,B_335] :
      ( ~ v1_partfun1('#skF_7',A_334)
      | ~ v1_partfun1('#skF_6',A_334)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_334,B_335)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(splitLeft,[status(thm)],[c_1800])).

tff(c_3103,plain,
    ( ~ v1_partfun1('#skF_7','#skF_4')
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_74,c_3100])).

tff(c_3107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1226,c_1222,c_3103])).

tff(c_3108,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1800])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_3120,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3108,c_68])).

tff(c_64,plain,(
    ! [D_59,A_53,B_54,C_55] :
      ( k1_funct_1(D_59,'#skF_3'(A_53,B_54,C_55,D_59)) != k1_funct_1(C_55,'#skF_3'(A_53,B_54,C_55,D_59))
      | r2_relset_1(A_53,B_54,C_55,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(D_59,A_53,B_54)
      | ~ v1_funct_1(D_59)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(C_55,A_53,B_54)
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_4175,plain,(
    ! [A_413,B_414,C_415] :
      ( r2_relset_1(A_413,B_414,C_415,C_415)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414)))
      | ~ v1_funct_2(C_415,A_413,B_414)
      | ~ v1_funct_1(C_415)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414)))
      | ~ v1_funct_2(C_415,A_413,B_414)
      | ~ v1_funct_1(C_415) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_64])).

tff(c_4177,plain,
    ( r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_4175])).

tff(c_4180,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_4177])).

tff(c_4182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3120,c_4180])).

tff(c_4183,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4189,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4183,c_6])).

tff(c_4184,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4194,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4183,c_4184])).

tff(c_4235,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4194,c_80])).

tff(c_4209,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4194,c_82])).

tff(c_58,plain,(
    ! [C_47,B_46] :
      ( v1_partfun1(C_47,k1_xboole_0)
      | ~ v1_funct_2(C_47,k1_xboole_0,B_46)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_46)))
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_5272,plain,(
    ! [C_523,B_524] :
      ( v1_partfun1(C_523,'#skF_4')
      | ~ v1_funct_2(C_523,'#skF_4',B_524)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_524)))
      | ~ v1_funct_1(C_523) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4183,c_4183,c_4183,c_58])).

tff(c_5275,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4235,c_5272])).

tff(c_5281,plain,(
    v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4209,c_5275])).

tff(c_4199,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4194,c_76])).

tff(c_4234,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4194,c_74])).

tff(c_5278,plain,
    ( v1_partfun1('#skF_7','#skF_4')
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4234,c_5272])).

tff(c_5284,plain,(
    v1_partfun1('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4199,c_5278])).

tff(c_5863,plain,(
    ! [D_581,C_582,A_583,B_584] :
      ( D_581 = C_582
      | ~ r1_partfun1(C_582,D_581)
      | ~ v1_partfun1(D_581,A_583)
      | ~ v1_partfun1(C_582,A_583)
      | ~ m1_subset_1(D_581,k1_zfmisc_1(k2_zfmisc_1(A_583,B_584)))
      | ~ v1_funct_1(D_581)
      | ~ m1_subset_1(C_582,k1_zfmisc_1(k2_zfmisc_1(A_583,B_584)))
      | ~ v1_funct_1(C_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_5867,plain,(
    ! [A_583,B_584] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_583)
      | ~ v1_partfun1('#skF_6',A_583)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_583,B_584)))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_583,B_584)))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_5863])).

tff(c_5873,plain,(
    ! [A_583,B_584] :
      ( '#skF_7' = '#skF_6'
      | ~ v1_partfun1('#skF_7',A_583)
      | ~ v1_partfun1('#skF_6',A_583)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_583,B_584)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_583,B_584))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_78,c_5867])).

tff(c_6191,plain,(
    ! [A_610,B_611] :
      ( ~ v1_partfun1('#skF_7',A_610)
      | ~ v1_partfun1('#skF_6',A_610)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_610,B_611)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_610,B_611))) ) ),
    inference(splitLeft,[status(thm)],[c_5873])).

tff(c_6194,plain,
    ( ~ v1_partfun1('#skF_7','#skF_4')
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_4234,c_6191])).

tff(c_6198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_5281,c_5284,c_6194])).

tff(c_6199,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5873])).

tff(c_4228,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4194,c_68])).

tff(c_6211,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6199,c_4228])).

tff(c_6256,plain,(
    ! [A_614,B_615,C_616,D_617] :
      ( r2_hidden('#skF_3'(A_614,B_615,C_616,D_617),A_614)
      | r2_relset_1(A_614,B_615,C_616,D_617)
      | ~ m1_subset_1(D_617,k1_zfmisc_1(k2_zfmisc_1(A_614,B_615)))
      | ~ v1_funct_2(D_617,A_614,B_615)
      | ~ v1_funct_1(D_617)
      | ~ m1_subset_1(C_616,k1_zfmisc_1(k2_zfmisc_1(A_614,B_615)))
      | ~ v1_funct_2(C_616,A_614,B_615)
      | ~ v1_funct_1(C_616) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_6258,plain,(
    ! [C_616] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_4',C_616,'#skF_6'),'#skF_4')
      | r2_relset_1('#skF_4','#skF_4',C_616,'#skF_6')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_616,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_2(C_616,'#skF_4','#skF_4')
      | ~ v1_funct_1(C_616) ) ),
    inference(resolution,[status(thm)],[c_4235,c_6256])).

tff(c_6312,plain,(
    ! [C_625] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_4',C_625,'#skF_6'),'#skF_4')
      | r2_relset_1('#skF_4','#skF_4',C_625,'#skF_6')
      | ~ m1_subset_1(C_625,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
      | ~ v1_funct_2(C_625,'#skF_4','#skF_4')
      | ~ v1_funct_1(C_625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4209,c_6258])).

tff(c_6315,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_4','#skF_6','#skF_6'),'#skF_4')
    | r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4235,c_6312])).

tff(c_6318,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_4','#skF_6','#skF_6'),'#skF_4')
    | r2_relset_1('#skF_4','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4209,c_6315])).

tff(c_6319,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_4','#skF_6','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_6211,c_6318])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6326,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6319,c_2])).

tff(c_6334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4189,c_6326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:34:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.57/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.57/2.31  
% 6.57/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.82/2.32  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3
% 6.82/2.32  
% 6.82/2.32  %Foreground sorts:
% 6.82/2.32  
% 6.82/2.32  
% 6.82/2.32  %Background operators:
% 6.82/2.32  
% 6.82/2.32  
% 6.82/2.32  %Foreground operators:
% 6.82/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.82/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.82/2.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.82/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.82/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.82/2.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.82/2.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.82/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.82/2.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.82/2.32  tff('#skF_7', type, '#skF_7': $i).
% 6.82/2.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.82/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.82/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.82/2.32  tff('#skF_6', type, '#skF_6': $i).
% 6.82/2.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.82/2.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.82/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.82/2.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.82/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.82/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.82/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.82/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.82/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.82/2.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.82/2.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.82/2.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.82/2.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.82/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.82/2.32  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 6.82/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.82/2.32  
% 6.82/2.33  tff(f_226, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 6.82/2.33  tff(f_166, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 6.82/2.33  tff(f_183, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 6.82/2.33  tff(f_203, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 6.82/2.33  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.82/2.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.82/2.33  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_70, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_104, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_70])).
% 6.82/2.33  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_82, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_1212, plain, (![B_185, C_186, A_187]: (k1_xboole_0=B_185 | v1_partfun1(C_186, A_187) | ~v1_funct_2(C_186, A_187, B_185) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_185))) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.82/2.33  tff(c_1218, plain, (k1_xboole_0='#skF_5' | v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_1212])).
% 6.82/2.33  tff(c_1225, plain, (k1_xboole_0='#skF_5' | v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_1218])).
% 6.82/2.33  tff(c_1226, plain, (v1_partfun1('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_104, c_1225])).
% 6.82/2.33  tff(c_78, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_76, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_74, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_1215, plain, (k1_xboole_0='#skF_5' | v1_partfun1('#skF_7', '#skF_4') | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_74, c_1212])).
% 6.82/2.33  tff(c_1221, plain, (k1_xboole_0='#skF_5' | v1_partfun1('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1215])).
% 6.82/2.33  tff(c_1222, plain, (v1_partfun1('#skF_7', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_104, c_1221])).
% 6.82/2.33  tff(c_72, plain, (r1_partfun1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_1790, plain, (![D_232, C_233, A_234, B_235]: (D_232=C_233 | ~r1_partfun1(C_233, D_232) | ~v1_partfun1(D_232, A_234) | ~v1_partfun1(C_233, A_234) | ~m1_subset_1(D_232, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(D_232) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(C_233))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.82/2.33  tff(c_1794, plain, (![A_234, B_235]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_234) | ~v1_partfun1('#skF_6', A_234) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_1790])).
% 6.82/2.33  tff(c_1800, plain, (![A_234, B_235]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_234) | ~v1_partfun1('#skF_6', A_234) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_78, c_1794])).
% 6.82/2.33  tff(c_3100, plain, (![A_334, B_335]: (~v1_partfun1('#skF_7', A_334) | ~v1_partfun1('#skF_6', A_334) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(splitLeft, [status(thm)], [c_1800])).
% 6.82/2.33  tff(c_3103, plain, (~v1_partfun1('#skF_7', '#skF_4') | ~v1_partfun1('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_74, c_3100])).
% 6.82/2.33  tff(c_3107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_1226, c_1222, c_3103])).
% 6.82/2.33  tff(c_3108, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_1800])).
% 6.82/2.33  tff(c_68, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.82/2.33  tff(c_3120, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3108, c_68])).
% 6.82/2.33  tff(c_64, plain, (![D_59, A_53, B_54, C_55]: (k1_funct_1(D_59, '#skF_3'(A_53, B_54, C_55, D_59))!=k1_funct_1(C_55, '#skF_3'(A_53, B_54, C_55, D_59)) | r2_relset_1(A_53, B_54, C_55, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(D_59, A_53, B_54) | ~v1_funct_1(D_59) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(C_55, A_53, B_54) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.82/2.33  tff(c_4175, plain, (![A_413, B_414, C_415]: (r2_relset_1(A_413, B_414, C_415, C_415) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))) | ~v1_funct_2(C_415, A_413, B_414) | ~v1_funct_1(C_415) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))) | ~v1_funct_2(C_415, A_413, B_414) | ~v1_funct_1(C_415))), inference(reflexivity, [status(thm), theory('equality')], [c_64])).
% 6.82/2.33  tff(c_4177, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_4175])).
% 6.82/2.33  tff(c_4180, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_4177])).
% 6.82/2.33  tff(c_4182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3120, c_4180])).
% 6.82/2.33  tff(c_4183, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_70])).
% 6.82/2.33  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.82/2.33  tff(c_4189, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4183, c_6])).
% 6.82/2.33  tff(c_4184, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_70])).
% 6.82/2.33  tff(c_4194, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4183, c_4184])).
% 6.82/2.33  tff(c_4235, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4194, c_80])).
% 6.82/2.33  tff(c_4209, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4194, c_82])).
% 6.82/2.33  tff(c_58, plain, (![C_47, B_46]: (v1_partfun1(C_47, k1_xboole_0) | ~v1_funct_2(C_47, k1_xboole_0, B_46) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_46))) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.82/2.33  tff(c_5272, plain, (![C_523, B_524]: (v1_partfun1(C_523, '#skF_4') | ~v1_funct_2(C_523, '#skF_4', B_524) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_524))) | ~v1_funct_1(C_523))), inference(demodulation, [status(thm), theory('equality')], [c_4183, c_4183, c_4183, c_58])).
% 6.82/2.33  tff(c_5275, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_4235, c_5272])).
% 6.82/2.33  tff(c_5281, plain, (v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4209, c_5275])).
% 6.82/2.33  tff(c_4199, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4194, c_76])).
% 6.82/2.33  tff(c_4234, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4194, c_74])).
% 6.82/2.33  tff(c_5278, plain, (v1_partfun1('#skF_7', '#skF_4') | ~v1_funct_2('#skF_7', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_4234, c_5272])).
% 6.82/2.33  tff(c_5284, plain, (v1_partfun1('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4199, c_5278])).
% 6.82/2.33  tff(c_5863, plain, (![D_581, C_582, A_583, B_584]: (D_581=C_582 | ~r1_partfun1(C_582, D_581) | ~v1_partfun1(D_581, A_583) | ~v1_partfun1(C_582, A_583) | ~m1_subset_1(D_581, k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))) | ~v1_funct_1(D_581) | ~m1_subset_1(C_582, k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))) | ~v1_funct_1(C_582))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.82/2.33  tff(c_5867, plain, (![A_583, B_584]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_583) | ~v1_partfun1('#skF_6', A_583) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_5863])).
% 6.82/2.33  tff(c_5873, plain, (![A_583, B_584]: ('#skF_7'='#skF_6' | ~v1_partfun1('#skF_7', A_583) | ~v1_partfun1('#skF_6', A_583) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_78, c_5867])).
% 6.82/2.33  tff(c_6191, plain, (![A_610, B_611]: (~v1_partfun1('#skF_7', A_610) | ~v1_partfun1('#skF_6', A_610) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_610, B_611))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_610, B_611))))), inference(splitLeft, [status(thm)], [c_5873])).
% 6.82/2.33  tff(c_6194, plain, (~v1_partfun1('#skF_7', '#skF_4') | ~v1_partfun1('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_4234, c_6191])).
% 6.82/2.33  tff(c_6198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4235, c_5281, c_5284, c_6194])).
% 6.82/2.33  tff(c_6199, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_5873])).
% 6.82/2.33  tff(c_4228, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4194, c_68])).
% 6.82/2.33  tff(c_6211, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6199, c_4228])).
% 6.82/2.33  tff(c_6256, plain, (![A_614, B_615, C_616, D_617]: (r2_hidden('#skF_3'(A_614, B_615, C_616, D_617), A_614) | r2_relset_1(A_614, B_615, C_616, D_617) | ~m1_subset_1(D_617, k1_zfmisc_1(k2_zfmisc_1(A_614, B_615))) | ~v1_funct_2(D_617, A_614, B_615) | ~v1_funct_1(D_617) | ~m1_subset_1(C_616, k1_zfmisc_1(k2_zfmisc_1(A_614, B_615))) | ~v1_funct_2(C_616, A_614, B_615) | ~v1_funct_1(C_616))), inference(cnfTransformation, [status(thm)], [f_203])).
% 6.82/2.33  tff(c_6258, plain, (![C_616]: (r2_hidden('#skF_3'('#skF_4', '#skF_4', C_616, '#skF_6'), '#skF_4') | r2_relset_1('#skF_4', '#skF_4', C_616, '#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_616, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_2(C_616, '#skF_4', '#skF_4') | ~v1_funct_1(C_616))), inference(resolution, [status(thm)], [c_4235, c_6256])).
% 6.82/2.33  tff(c_6312, plain, (![C_625]: (r2_hidden('#skF_3'('#skF_4', '#skF_4', C_625, '#skF_6'), '#skF_4') | r2_relset_1('#skF_4', '#skF_4', C_625, '#skF_6') | ~m1_subset_1(C_625, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~v1_funct_2(C_625, '#skF_4', '#skF_4') | ~v1_funct_1(C_625))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4209, c_6258])).
% 6.82/2.33  tff(c_6315, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_4', '#skF_6', '#skF_6'), '#skF_4') | r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_4235, c_6312])).
% 6.82/2.33  tff(c_6318, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_4', '#skF_6', '#skF_6'), '#skF_4') | r2_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4209, c_6315])).
% 6.82/2.33  tff(c_6319, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_4', '#skF_6', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_6211, c_6318])).
% 6.82/2.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.82/2.33  tff(c_6326, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6319, c_2])).
% 6.82/2.33  tff(c_6334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4189, c_6326])).
% 6.82/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.82/2.33  
% 6.82/2.33  Inference rules
% 6.82/2.33  ----------------------
% 6.82/2.33  #Ref     : 25
% 6.82/2.33  #Sup     : 1334
% 6.82/2.33  #Fact    : 0
% 6.82/2.33  #Define  : 0
% 6.82/2.33  #Split   : 5
% 6.82/2.33  #Chain   : 0
% 6.82/2.33  #Close   : 0
% 6.82/2.33  
% 6.82/2.33  Ordering : KBO
% 6.82/2.33  
% 6.82/2.33  Simplification rules
% 6.82/2.33  ----------------------
% 6.82/2.34  #Subsume      : 208
% 6.82/2.34  #Demod        : 1395
% 6.82/2.34  #Tautology    : 789
% 6.82/2.34  #SimpNegUnit  : 8
% 6.82/2.34  #BackRed      : 35
% 6.82/2.34  
% 6.82/2.34  #Partial instantiations: 0
% 6.82/2.34  #Strategies tried      : 1
% 6.82/2.34  
% 6.82/2.34  Timing (in seconds)
% 6.82/2.34  ----------------------
% 6.82/2.34  Preprocessing        : 0.37
% 6.82/2.34  Parsing              : 0.20
% 6.82/2.34  CNF conversion       : 0.03
% 6.82/2.34  Main loop            : 1.17
% 6.82/2.34  Inferencing          : 0.40
% 6.82/2.34  Reduction            : 0.38
% 6.82/2.34  Demodulation         : 0.28
% 6.82/2.34  BG Simplification    : 0.04
% 6.82/2.34  Subsumption          : 0.25
% 6.82/2.34  Abstraction          : 0.05
% 6.82/2.34  MUC search           : 0.00
% 6.82/2.34  Cooper               : 0.00
% 6.82/2.34  Total                : 1.58
% 6.82/2.34  Index Insertion      : 0.00
% 6.82/2.34  Index Deletion       : 0.00
% 6.82/2.34  Index Matching       : 0.00
% 6.82/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
