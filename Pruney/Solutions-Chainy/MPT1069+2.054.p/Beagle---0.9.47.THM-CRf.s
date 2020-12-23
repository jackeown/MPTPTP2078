%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:53 EST 2020

% Result     : Theorem 6.35s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 772 expanded)
%              Number of leaves         :   49 ( 282 expanded)
%              Depth                    :   17
%              Number of atoms          :  339 (2402 expanded)
%              Number of equality atoms :   88 ( 567 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_165,axiom,(
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

tff(f_130,axiom,(
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

tff(f_141,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
             => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                  & ! [D] :
                      ( m1_subset_1(D,B)
                     => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_104,plain,(
    ! [B_93,A_94] :
      ( v1_relat_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_68,c_104])).

tff(c_116,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_110])).

tff(c_62,plain,(
    m1_subset_1('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_72,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_70,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_231,plain,(
    ! [A_126,B_127,C_128] :
      ( k2_relset_1(A_126,B_127,C_128) = k2_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_239,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_231])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_178,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_185,plain,(
    k1_relset_1('#skF_7','#skF_5','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_178])).

tff(c_60,plain,(
    r1_tarski(k2_relset_1('#skF_6','#skF_7','#skF_8'),k1_relset_1('#skF_7','#skF_5','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_187,plain,(
    r1_tarski(k2_relset_1('#skF_6','#skF_7','#skF_8'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_60])).

tff(c_244,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_187])).

tff(c_66,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_2111,plain,(
    ! [C_331,B_333,E_336,A_332,F_335,D_334] :
      ( k1_funct_1(k8_funct_2(B_333,C_331,A_332,D_334,E_336),F_335) = k1_funct_1(E_336,k1_funct_1(D_334,F_335))
      | k1_xboole_0 = B_333
      | ~ r1_tarski(k2_relset_1(B_333,C_331,D_334),k1_relset_1(C_331,A_332,E_336))
      | ~ m1_subset_1(F_335,B_333)
      | ~ m1_subset_1(E_336,k1_zfmisc_1(k2_zfmisc_1(C_331,A_332)))
      | ~ v1_funct_1(E_336)
      | ~ m1_subset_1(D_334,k1_zfmisc_1(k2_zfmisc_1(B_333,C_331)))
      | ~ v1_funct_2(D_334,B_333,C_331)
      | ~ v1_funct_1(D_334)
      | v1_xboole_0(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2119,plain,(
    ! [B_333,D_334,F_335] :
      ( k1_funct_1(k8_funct_2(B_333,'#skF_7','#skF_5',D_334,'#skF_9'),F_335) = k1_funct_1('#skF_9',k1_funct_1(D_334,F_335))
      | k1_xboole_0 = B_333
      | ~ r1_tarski(k2_relset_1(B_333,'#skF_7',D_334),k1_relat_1('#skF_9'))
      | ~ m1_subset_1(F_335,B_333)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_5')))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(D_334,k1_zfmisc_1(k2_zfmisc_1(B_333,'#skF_7')))
      | ~ v1_funct_2(D_334,B_333,'#skF_7')
      | ~ v1_funct_1(D_334)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_2111])).

tff(c_2133,plain,(
    ! [B_333,D_334,F_335] :
      ( k1_funct_1(k8_funct_2(B_333,'#skF_7','#skF_5',D_334,'#skF_9'),F_335) = k1_funct_1('#skF_9',k1_funct_1(D_334,F_335))
      | k1_xboole_0 = B_333
      | ~ r1_tarski(k2_relset_1(B_333,'#skF_7',D_334),k1_relat_1('#skF_9'))
      | ~ m1_subset_1(F_335,B_333)
      | ~ m1_subset_1(D_334,k1_zfmisc_1(k2_zfmisc_1(B_333,'#skF_7')))
      | ~ v1_funct_2(D_334,B_333,'#skF_7')
      | ~ v1_funct_1(D_334)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2119])).

tff(c_2527,plain,(
    ! [B_351,D_352,F_353] :
      ( k1_funct_1(k8_funct_2(B_351,'#skF_7','#skF_5',D_352,'#skF_9'),F_353) = k1_funct_1('#skF_9',k1_funct_1(D_352,F_353))
      | k1_xboole_0 = B_351
      | ~ r1_tarski(k2_relset_1(B_351,'#skF_7',D_352),k1_relat_1('#skF_9'))
      | ~ m1_subset_1(F_353,B_351)
      | ~ m1_subset_1(D_352,k1_zfmisc_1(k2_zfmisc_1(B_351,'#skF_7')))
      | ~ v1_funct_2(D_352,B_351,'#skF_7')
      | ~ v1_funct_1(D_352) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2133])).

tff(c_2529,plain,(
    ! [F_353] :
      ( k1_funct_1(k8_funct_2('#skF_6','#skF_7','#skF_5','#skF_8','#skF_9'),F_353) = k1_funct_1('#skF_9',k1_funct_1('#skF_8',F_353))
      | k1_xboole_0 = '#skF_6'
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_relat_1('#skF_9'))
      | ~ m1_subset_1(F_353,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_2527])).

tff(c_2534,plain,(
    ! [F_353] :
      ( k1_funct_1(k8_funct_2('#skF_6','#skF_7','#skF_5','#skF_8','#skF_9'),F_353) = k1_funct_1('#skF_9',k1_funct_1('#skF_8',F_353))
      | k1_xboole_0 = '#skF_6'
      | ~ m1_subset_1(F_353,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_244,c_2529])).

tff(c_2535,plain,(
    ! [F_353] :
      ( k1_funct_1(k8_funct_2('#skF_6','#skF_7','#skF_5','#skF_8','#skF_9'),F_353) = k1_funct_1('#skF_9',k1_funct_1('#skF_8',F_353))
      | ~ m1_subset_1(F_353,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2534])).

tff(c_186,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_178])).

tff(c_1554,plain,(
    ! [B_293,A_294,C_295] :
      ( k1_xboole_0 = B_293
      | k1_relset_1(A_294,B_293,C_295) = A_294
      | ~ v1_funct_2(C_295,A_294,B_293)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_294,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1572,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_1554])).

tff(c_1581,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_186,c_1572])).

tff(c_1582,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1581])).

tff(c_1655,plain,(
    ! [A_302,B_303,C_304] :
      ( k7_partfun1(A_302,B_303,C_304) = k1_funct_1(B_303,C_304)
      | ~ r2_hidden(C_304,k1_relat_1(B_303))
      | ~ v1_funct_1(B_303)
      | ~ v5_relat_1(B_303,A_302)
      | ~ v1_relat_1(B_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1657,plain,(
    ! [A_302,C_304] :
      ( k7_partfun1(A_302,'#skF_8',C_304) = k1_funct_1('#skF_8',C_304)
      | ~ r2_hidden(C_304,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_302)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1582,c_1655])).

tff(c_1728,plain,(
    ! [A_305,C_306] :
      ( k7_partfun1(A_305,'#skF_8',C_306) = k1_funct_1('#skF_8',C_306)
      | ~ r2_hidden(C_306,'#skF_6')
      | ~ v5_relat_1('#skF_8',A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_72,c_1657])).

tff(c_1775,plain,(
    ! [A_305] :
      ( k7_partfun1(A_305,'#skF_8','#skF_1'('#skF_6')) = k1_funct_1('#skF_8','#skF_1'('#skF_6'))
      | ~ v5_relat_1('#skF_8',A_305)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_1728])).

tff(c_1840,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1775])).

tff(c_77,plain,(
    ! [A_86] :
      ( r2_hidden('#skF_3'(A_86),A_86)
      | k1_xboole_0 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_86] :
      ( ~ v1_xboole_0(A_86)
      | k1_xboole_0 = A_86 ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_1843,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1840,c_81])).

tff(c_1847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1843])).

tff(c_1849,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( v5_relat_1(B_18,A_17)
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_254,plain,
    ( v5_relat_1('#skF_8',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_244,c_20])).

tff(c_258,plain,(
    v5_relat_1('#skF_8',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_254])).

tff(c_26,plain,(
    ! [C_23,B_22,A_21] :
      ( m1_subset_1(k1_funct_1(C_23,B_22),A_21)
      | ~ r2_hidden(B_22,k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v5_relat_1(C_23,A_21)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1586,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_22),A_21)
      | ~ r2_hidden(B_22,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_21)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1582,c_26])).

tff(c_1590,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_22),A_21)
      | ~ r2_hidden(B_22,'#skF_6')
      | ~ v5_relat_1('#skF_8',A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_72,c_1586])).

tff(c_138,plain,(
    ! [C_103,B_104,A_105] :
      ( r2_hidden(C_103,B_104)
      | ~ r2_hidden(C_103,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_197,plain,(
    ! [A_120,B_121] :
      ( r2_hidden('#skF_1'(A_120),B_121)
      | ~ r1_tarski(A_120,B_121)
      | v1_xboole_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_205,plain,(
    ! [B_122,A_123] :
      ( ~ v1_xboole_0(B_122)
      | ~ r1_tarski(A_123,B_122)
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_218,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | v1_xboole_0(k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_187,c_205])).

tff(c_222,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_107,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_104])).

tff(c_113,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_107])).

tff(c_129,plain,(
    ! [C_100,B_101,A_102] :
      ( v5_relat_1(C_100,B_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_136,plain,(
    v5_relat_1('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_129])).

tff(c_3378,plain,(
    ! [A_410,B_411,A_412] :
      ( k7_partfun1(A_410,B_411,A_412) = k1_funct_1(B_411,A_412)
      | ~ v1_funct_1(B_411)
      | ~ v5_relat_1(B_411,A_410)
      | ~ v1_relat_1(B_411)
      | v1_xboole_0(k1_relat_1(B_411))
      | ~ m1_subset_1(A_412,k1_relat_1(B_411)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1655])).

tff(c_3388,plain,(
    ! [A_412] :
      ( k7_partfun1('#skF_5','#skF_9',A_412) = k1_funct_1('#skF_9',A_412)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | v1_xboole_0(k1_relat_1('#skF_9'))
      | ~ m1_subset_1(A_412,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_136,c_3378])).

tff(c_3404,plain,(
    ! [A_412] :
      ( k7_partfun1('#skF_5','#skF_9',A_412) = k1_funct_1('#skF_9',A_412)
      | v1_xboole_0(k1_relat_1('#skF_9'))
      | ~ m1_subset_1(A_412,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_66,c_3388])).

tff(c_3426,plain,(
    ! [A_414] :
      ( k7_partfun1('#skF_5','#skF_9',A_414) = k1_funct_1('#skF_9',A_414)
      | ~ m1_subset_1(A_414,k1_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_3404])).

tff(c_3462,plain,(
    ! [B_22] :
      ( k7_partfun1('#skF_5','#skF_9',k1_funct_1('#skF_8',B_22)) = k1_funct_1('#skF_9',k1_funct_1('#skF_8',B_22))
      | ~ r2_hidden(B_22,'#skF_6')
      | ~ v5_relat_1('#skF_8',k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1590,c_3426])).

tff(c_3705,plain,(
    ! [B_428] :
      ( k7_partfun1('#skF_5','#skF_9',k1_funct_1('#skF_8',B_428)) = k1_funct_1('#skF_9',k1_funct_1('#skF_8',B_428))
      | ~ r2_hidden(B_428,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_3462])).

tff(c_56,plain,(
    k7_partfun1('#skF_5','#skF_9',k1_funct_1('#skF_8','#skF_10')) != k1_funct_1(k8_funct_2('#skF_6','#skF_7','#skF_5','#skF_8','#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_3717,plain,
    ( k1_funct_1(k8_funct_2('#skF_6','#skF_7','#skF_5','#skF_8','#skF_9'),'#skF_10') != k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_10'))
    | ~ r2_hidden('#skF_10','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3705,c_56])).

tff(c_3733,plain,(
    ~ r2_hidden('#skF_10','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3717])).

tff(c_3736,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_3733])).

tff(c_3739,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3736])).

tff(c_3741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1849,c_3739])).

tff(c_3742,plain,(
    k1_funct_1(k8_funct_2('#skF_6','#skF_7','#skF_5','#skF_8','#skF_9'),'#skF_10') != k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_3717])).

tff(c_3874,plain,(
    ~ m1_subset_1('#skF_10','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2535,c_3742])).

tff(c_3878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3874])).

tff(c_3879,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1581])).

tff(c_3898,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3879,c_12])).

tff(c_3901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3898])).

tff(c_3902,plain,(
    v1_xboole_0(k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_3919,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3902,c_81])).

tff(c_3924,plain,(
    ! [A_436,B_437,C_438] :
      ( k2_relset_1(A_436,B_437,C_438) = k2_relat_1(C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(A_436,B_437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3932,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_3924])).

tff(c_3943,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3919,c_3932])).

tff(c_117,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_2'(A_95,B_96),A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ! [A_95,B_96] :
      ( ~ v1_xboole_0(A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_160,plain,(
    ! [B_109,A_110] :
      ( v5_relat_1(B_109,A_110)
      | ~ r1_tarski(k2_relat_1(B_109),A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_169,plain,(
    ! [B_109,B_96] :
      ( v5_relat_1(B_109,B_96)
      | ~ v1_relat_1(B_109)
      | ~ v1_xboole_0(k2_relat_1(B_109)) ) ),
    inference(resolution,[status(thm)],[c_126,c_160])).

tff(c_3949,plain,(
    ! [B_96] :
      ( v5_relat_1('#skF_8',B_96)
      | ~ v1_relat_1('#skF_8')
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3943,c_169])).

tff(c_3961,plain,(
    ! [B_96] : v5_relat_1('#skF_8',B_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_116,c_3949])).

tff(c_3903,plain,(
    v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_3907,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3903,c_81])).

tff(c_3910,plain,(
    k1_relset_1('#skF_7','#skF_5','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3907,c_185])).

tff(c_4463,plain,(
    ! [B_516,C_517,A_518] :
      ( k1_xboole_0 = B_516
      | v1_funct_2(C_517,A_518,B_516)
      | k1_relset_1(A_518,B_516,C_517) != A_518
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(A_518,B_516))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4470,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_9','#skF_7','#skF_5')
    | k1_relset_1('#skF_7','#skF_5','#skF_9') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_64,c_4463])).

tff(c_4476,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_funct_2('#skF_9','#skF_7','#skF_5')
    | k1_xboole_0 != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3910,c_4470])).

tff(c_4479,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4476])).

tff(c_4608,plain,(
    ! [B_539,A_540,C_541] :
      ( k1_xboole_0 = B_539
      | k1_relset_1(A_540,B_539,C_541) = A_540
      | ~ v1_funct_2(C_541,A_540,B_539)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(A_540,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4618,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_4608])).

tff(c_4625,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_186,c_4618])).

tff(c_4626,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_4479,c_4625])).

tff(c_4724,plain,(
    ! [A_548,B_549,C_550] :
      ( k7_partfun1(A_548,B_549,C_550) = k1_funct_1(B_549,C_550)
      | ~ r2_hidden(C_550,k1_relat_1(B_549))
      | ~ v1_funct_1(B_549)
      | ~ v5_relat_1(B_549,A_548)
      | ~ v1_relat_1(B_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4726,plain,(
    ! [A_548,C_550] :
      ( k7_partfun1(A_548,'#skF_8',C_550) = k1_funct_1('#skF_8',C_550)
      | ~ r2_hidden(C_550,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_548)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4626,c_4724])).

tff(c_4770,plain,(
    ! [A_552,C_553] :
      ( k7_partfun1(A_552,'#skF_8',C_553) = k1_funct_1('#skF_8',C_553)
      | ~ r2_hidden(C_553,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_3961,c_72,c_4726])).

tff(c_4805,plain,(
    ! [A_552] :
      ( k7_partfun1(A_552,'#skF_8','#skF_1'('#skF_6')) = k1_funct_1('#skF_8','#skF_1'('#skF_6'))
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_4770])).

tff(c_4816,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4805])).

tff(c_4819,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4816,c_81])).

tff(c_4823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4819])).

tff(c_4825,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_4805])).

tff(c_4627,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_186])).

tff(c_5042,plain,(
    ! [A_578,B_579,C_580] :
      ( r2_hidden('#skF_4'(A_578,B_579,C_580),k2_relset_1(A_578,B_579,C_580))
      | k1_relset_1(A_578,B_579,C_580) = k1_xboole_0
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1(A_578,B_579)))
      | v1_xboole_0(B_579)
      | v1_xboole_0(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5056,plain,
    ( r2_hidden('#skF_4'('#skF_6','#skF_7','#skF_8'),k1_xboole_0)
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_xboole_0
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
    | v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3919,c_5042])).

tff(c_5063,plain,
    ( r2_hidden('#skF_4'('#skF_6','#skF_7','#skF_8'),k1_xboole_0)
    | k1_xboole_0 = '#skF_6'
    | v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4627,c_5056])).

tff(c_5064,plain,(
    r2_hidden('#skF_4'('#skF_6','#skF_7','#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_4825,c_74,c_58,c_5063])).

tff(c_5071,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5064,c_2])).

tff(c_5079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5071])).

tff(c_5081,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4476])).

tff(c_5110,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5081,c_12])).

tff(c_5113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.35/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.36  
% 6.60/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 6.60/2.36  
% 6.60/2.36  %Foreground sorts:
% 6.60/2.36  
% 6.60/2.36  
% 6.60/2.36  %Background operators:
% 6.60/2.36  
% 6.60/2.36  
% 6.60/2.36  %Foreground operators:
% 6.60/2.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.60/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.60/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.60/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.60/2.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.60/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.60/2.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.60/2.36  tff('#skF_7', type, '#skF_7': $i).
% 6.60/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.60/2.36  tff('#skF_10', type, '#skF_10': $i).
% 6.60/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.60/2.36  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 6.60/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.60/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.60/2.36  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 6.60/2.36  tff('#skF_6', type, '#skF_6': $i).
% 6.60/2.36  tff('#skF_9', type, '#skF_9': $i).
% 6.60/2.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.60/2.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.60/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.60/2.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.60/2.36  tff('#skF_8', type, '#skF_8': $i).
% 6.60/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.60/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.60/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.60/2.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.60/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.60/2.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.60/2.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.60/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.60/2.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.60/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.60/2.36  
% 6.60/2.38  tff(f_190, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 6.60/2.38  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.60/2.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.60/2.38  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.60/2.38  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.60/2.39  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.60/2.39  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.60/2.39  tff(f_165, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 6.60/2.39  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.60/2.39  tff(f_141, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 6.60/2.39  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.60/2.39  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.60/2.39  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.60/2.39  tff(f_78, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 6.60/2.39  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.60/2.39  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.60/2.39  tff(f_112, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 6.60/2.39  tff(c_74, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.60/2.39  tff(c_58, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.60/2.39  tff(c_24, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.60/2.39  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_104, plain, (![B_93, A_94]: (v1_relat_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.60/2.39  tff(c_110, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_104])).
% 6.60/2.39  tff(c_116, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_110])).
% 6.60/2.39  tff(c_62, plain, (m1_subset_1('#skF_10', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_72, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_70, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_231, plain, (![A_126, B_127, C_128]: (k2_relset_1(A_126, B_127, C_128)=k2_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.60/2.39  tff(c_239, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_231])).
% 6.60/2.39  tff(c_64, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_178, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.60/2.39  tff(c_185, plain, (k1_relset_1('#skF_7', '#skF_5', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_64, c_178])).
% 6.60/2.39  tff(c_60, plain, (r1_tarski(k2_relset_1('#skF_6', '#skF_7', '#skF_8'), k1_relset_1('#skF_7', '#skF_5', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_187, plain, (r1_tarski(k2_relset_1('#skF_6', '#skF_7', '#skF_8'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_60])).
% 6.60/2.39  tff(c_244, plain, (r1_tarski(k2_relat_1('#skF_8'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_187])).
% 6.60/2.39  tff(c_66, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_2111, plain, (![C_331, B_333, E_336, A_332, F_335, D_334]: (k1_funct_1(k8_funct_2(B_333, C_331, A_332, D_334, E_336), F_335)=k1_funct_1(E_336, k1_funct_1(D_334, F_335)) | k1_xboole_0=B_333 | ~r1_tarski(k2_relset_1(B_333, C_331, D_334), k1_relset_1(C_331, A_332, E_336)) | ~m1_subset_1(F_335, B_333) | ~m1_subset_1(E_336, k1_zfmisc_1(k2_zfmisc_1(C_331, A_332))) | ~v1_funct_1(E_336) | ~m1_subset_1(D_334, k1_zfmisc_1(k2_zfmisc_1(B_333, C_331))) | ~v1_funct_2(D_334, B_333, C_331) | ~v1_funct_1(D_334) | v1_xboole_0(C_331))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.60/2.39  tff(c_2119, plain, (![B_333, D_334, F_335]: (k1_funct_1(k8_funct_2(B_333, '#skF_7', '#skF_5', D_334, '#skF_9'), F_335)=k1_funct_1('#skF_9', k1_funct_1(D_334, F_335)) | k1_xboole_0=B_333 | ~r1_tarski(k2_relset_1(B_333, '#skF_7', D_334), k1_relat_1('#skF_9')) | ~m1_subset_1(F_335, B_333) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_5'))) | ~v1_funct_1('#skF_9') | ~m1_subset_1(D_334, k1_zfmisc_1(k2_zfmisc_1(B_333, '#skF_7'))) | ~v1_funct_2(D_334, B_333, '#skF_7') | ~v1_funct_1(D_334) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_2111])).
% 6.60/2.39  tff(c_2133, plain, (![B_333, D_334, F_335]: (k1_funct_1(k8_funct_2(B_333, '#skF_7', '#skF_5', D_334, '#skF_9'), F_335)=k1_funct_1('#skF_9', k1_funct_1(D_334, F_335)) | k1_xboole_0=B_333 | ~r1_tarski(k2_relset_1(B_333, '#skF_7', D_334), k1_relat_1('#skF_9')) | ~m1_subset_1(F_335, B_333) | ~m1_subset_1(D_334, k1_zfmisc_1(k2_zfmisc_1(B_333, '#skF_7'))) | ~v1_funct_2(D_334, B_333, '#skF_7') | ~v1_funct_1(D_334) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2119])).
% 6.60/2.39  tff(c_2527, plain, (![B_351, D_352, F_353]: (k1_funct_1(k8_funct_2(B_351, '#skF_7', '#skF_5', D_352, '#skF_9'), F_353)=k1_funct_1('#skF_9', k1_funct_1(D_352, F_353)) | k1_xboole_0=B_351 | ~r1_tarski(k2_relset_1(B_351, '#skF_7', D_352), k1_relat_1('#skF_9')) | ~m1_subset_1(F_353, B_351) | ~m1_subset_1(D_352, k1_zfmisc_1(k2_zfmisc_1(B_351, '#skF_7'))) | ~v1_funct_2(D_352, B_351, '#skF_7') | ~v1_funct_1(D_352))), inference(negUnitSimplification, [status(thm)], [c_74, c_2133])).
% 6.60/2.39  tff(c_2529, plain, (![F_353]: (k1_funct_1(k8_funct_2('#skF_6', '#skF_7', '#skF_5', '#skF_8', '#skF_9'), F_353)=k1_funct_1('#skF_9', k1_funct_1('#skF_8', F_353)) | k1_xboole_0='#skF_6' | ~r1_tarski(k2_relat_1('#skF_8'), k1_relat_1('#skF_9')) | ~m1_subset_1(F_353, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_2527])).
% 6.60/2.39  tff(c_2534, plain, (![F_353]: (k1_funct_1(k8_funct_2('#skF_6', '#skF_7', '#skF_5', '#skF_8', '#skF_9'), F_353)=k1_funct_1('#skF_9', k1_funct_1('#skF_8', F_353)) | k1_xboole_0='#skF_6' | ~m1_subset_1(F_353, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_244, c_2529])).
% 6.60/2.39  tff(c_2535, plain, (![F_353]: (k1_funct_1(k8_funct_2('#skF_6', '#skF_7', '#skF_5', '#skF_8', '#skF_9'), F_353)=k1_funct_1('#skF_9', k1_funct_1('#skF_8', F_353)) | ~m1_subset_1(F_353, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2534])).
% 6.60/2.39  tff(c_186, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_178])).
% 6.60/2.39  tff(c_1554, plain, (![B_293, A_294, C_295]: (k1_xboole_0=B_293 | k1_relset_1(A_294, B_293, C_295)=A_294 | ~v1_funct_2(C_295, A_294, B_293) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_294, B_293))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.60/2.39  tff(c_1572, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_1554])).
% 6.60/2.39  tff(c_1581, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_186, c_1572])).
% 6.60/2.39  tff(c_1582, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_1581])).
% 6.60/2.39  tff(c_1655, plain, (![A_302, B_303, C_304]: (k7_partfun1(A_302, B_303, C_304)=k1_funct_1(B_303, C_304) | ~r2_hidden(C_304, k1_relat_1(B_303)) | ~v1_funct_1(B_303) | ~v5_relat_1(B_303, A_302) | ~v1_relat_1(B_303))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.60/2.39  tff(c_1657, plain, (![A_302, C_304]: (k7_partfun1(A_302, '#skF_8', C_304)=k1_funct_1('#skF_8', C_304) | ~r2_hidden(C_304, '#skF_6') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_302) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1582, c_1655])).
% 6.60/2.39  tff(c_1728, plain, (![A_305, C_306]: (k7_partfun1(A_305, '#skF_8', C_306)=k1_funct_1('#skF_8', C_306) | ~r2_hidden(C_306, '#skF_6') | ~v5_relat_1('#skF_8', A_305))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_72, c_1657])).
% 6.60/2.39  tff(c_1775, plain, (![A_305]: (k7_partfun1(A_305, '#skF_8', '#skF_1'('#skF_6'))=k1_funct_1('#skF_8', '#skF_1'('#skF_6')) | ~v5_relat_1('#skF_8', A_305) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_1728])).
% 6.60/2.39  tff(c_1840, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1775])).
% 6.60/2.39  tff(c_77, plain, (![A_86]: (r2_hidden('#skF_3'(A_86), A_86) | k1_xboole_0=A_86)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.60/2.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.60/2.39  tff(c_81, plain, (![A_86]: (~v1_xboole_0(A_86) | k1_xboole_0=A_86)), inference(resolution, [status(thm)], [c_77, c_2])).
% 6.60/2.39  tff(c_1843, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1840, c_81])).
% 6.60/2.39  tff(c_1847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1843])).
% 6.60/2.39  tff(c_1849, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_1775])).
% 6.60/2.39  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.60/2.39  tff(c_20, plain, (![B_18, A_17]: (v5_relat_1(B_18, A_17) | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.60/2.39  tff(c_254, plain, (v5_relat_1('#skF_8', k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_244, c_20])).
% 6.60/2.39  tff(c_258, plain, (v5_relat_1('#skF_8', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_254])).
% 6.60/2.39  tff(c_26, plain, (![C_23, B_22, A_21]: (m1_subset_1(k1_funct_1(C_23, B_22), A_21) | ~r2_hidden(B_22, k1_relat_1(C_23)) | ~v1_funct_1(C_23) | ~v5_relat_1(C_23, A_21) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.60/2.39  tff(c_1586, plain, (![B_22, A_21]: (m1_subset_1(k1_funct_1('#skF_8', B_22), A_21) | ~r2_hidden(B_22, '#skF_6') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_21) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1582, c_26])).
% 6.60/2.39  tff(c_1590, plain, (![B_22, A_21]: (m1_subset_1(k1_funct_1('#skF_8', B_22), A_21) | ~r2_hidden(B_22, '#skF_6') | ~v5_relat_1('#skF_8', A_21))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_72, c_1586])).
% 6.60/2.39  tff(c_138, plain, (![C_103, B_104, A_105]: (r2_hidden(C_103, B_104) | ~r2_hidden(C_103, A_105) | ~r1_tarski(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.60/2.39  tff(c_197, plain, (![A_120, B_121]: (r2_hidden('#skF_1'(A_120), B_121) | ~r1_tarski(A_120, B_121) | v1_xboole_0(A_120))), inference(resolution, [status(thm)], [c_4, c_138])).
% 6.60/2.39  tff(c_205, plain, (![B_122, A_123]: (~v1_xboole_0(B_122) | ~r1_tarski(A_123, B_122) | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_197, c_2])).
% 6.60/2.39  tff(c_218, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | v1_xboole_0(k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_187, c_205])).
% 6.60/2.39  tff(c_222, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_218])).
% 6.60/2.39  tff(c_107, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_104])).
% 6.60/2.39  tff(c_113, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_107])).
% 6.60/2.39  tff(c_129, plain, (![C_100, B_101, A_102]: (v5_relat_1(C_100, B_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.60/2.39  tff(c_136, plain, (v5_relat_1('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_129])).
% 6.60/2.39  tff(c_3378, plain, (![A_410, B_411, A_412]: (k7_partfun1(A_410, B_411, A_412)=k1_funct_1(B_411, A_412) | ~v1_funct_1(B_411) | ~v5_relat_1(B_411, A_410) | ~v1_relat_1(B_411) | v1_xboole_0(k1_relat_1(B_411)) | ~m1_subset_1(A_412, k1_relat_1(B_411)))), inference(resolution, [status(thm)], [c_16, c_1655])).
% 6.60/2.39  tff(c_3388, plain, (![A_412]: (k7_partfun1('#skF_5', '#skF_9', A_412)=k1_funct_1('#skF_9', A_412) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | v1_xboole_0(k1_relat_1('#skF_9')) | ~m1_subset_1(A_412, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_136, c_3378])).
% 6.60/2.39  tff(c_3404, plain, (![A_412]: (k7_partfun1('#skF_5', '#skF_9', A_412)=k1_funct_1('#skF_9', A_412) | v1_xboole_0(k1_relat_1('#skF_9')) | ~m1_subset_1(A_412, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_66, c_3388])).
% 6.60/2.39  tff(c_3426, plain, (![A_414]: (k7_partfun1('#skF_5', '#skF_9', A_414)=k1_funct_1('#skF_9', A_414) | ~m1_subset_1(A_414, k1_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_222, c_3404])).
% 6.60/2.39  tff(c_3462, plain, (![B_22]: (k7_partfun1('#skF_5', '#skF_9', k1_funct_1('#skF_8', B_22))=k1_funct_1('#skF_9', k1_funct_1('#skF_8', B_22)) | ~r2_hidden(B_22, '#skF_6') | ~v5_relat_1('#skF_8', k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_1590, c_3426])).
% 6.60/2.39  tff(c_3705, plain, (![B_428]: (k7_partfun1('#skF_5', '#skF_9', k1_funct_1('#skF_8', B_428))=k1_funct_1('#skF_9', k1_funct_1('#skF_8', B_428)) | ~r2_hidden(B_428, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_3462])).
% 6.60/2.39  tff(c_56, plain, (k7_partfun1('#skF_5', '#skF_9', k1_funct_1('#skF_8', '#skF_10'))!=k1_funct_1(k8_funct_2('#skF_6', '#skF_7', '#skF_5', '#skF_8', '#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_190])).
% 6.60/2.39  tff(c_3717, plain, (k1_funct_1(k8_funct_2('#skF_6', '#skF_7', '#skF_5', '#skF_8', '#skF_9'), '#skF_10')!=k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_10')) | ~r2_hidden('#skF_10', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3705, c_56])).
% 6.60/2.39  tff(c_3733, plain, (~r2_hidden('#skF_10', '#skF_6')), inference(splitLeft, [status(thm)], [c_3717])).
% 6.60/2.39  tff(c_3736, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_10', '#skF_6')), inference(resolution, [status(thm)], [c_16, c_3733])).
% 6.60/2.39  tff(c_3739, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3736])).
% 6.60/2.39  tff(c_3741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1849, c_3739])).
% 6.60/2.39  tff(c_3742, plain, (k1_funct_1(k8_funct_2('#skF_6', '#skF_7', '#skF_5', '#skF_8', '#skF_9'), '#skF_10')!=k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_3717])).
% 6.60/2.39  tff(c_3874, plain, (~m1_subset_1('#skF_10', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2535, c_3742])).
% 6.60/2.39  tff(c_3878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_3874])).
% 6.60/2.39  tff(c_3879, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1581])).
% 6.60/2.39  tff(c_3898, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3879, c_12])).
% 6.60/2.39  tff(c_3901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3898])).
% 6.60/2.39  tff(c_3902, plain, (v1_xboole_0(k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_218])).
% 6.60/2.39  tff(c_3919, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_3902, c_81])).
% 6.60/2.39  tff(c_3924, plain, (![A_436, B_437, C_438]: (k2_relset_1(A_436, B_437, C_438)=k2_relat_1(C_438) | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(A_436, B_437))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.60/2.39  tff(c_3932, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_3924])).
% 6.60/2.39  tff(c_3943, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3919, c_3932])).
% 6.60/2.39  tff(c_117, plain, (![A_95, B_96]: (r2_hidden('#skF_2'(A_95, B_96), A_95) | r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.60/2.39  tff(c_126, plain, (![A_95, B_96]: (~v1_xboole_0(A_95) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_117, c_2])).
% 6.60/2.39  tff(c_160, plain, (![B_109, A_110]: (v5_relat_1(B_109, A_110) | ~r1_tarski(k2_relat_1(B_109), A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.60/2.39  tff(c_169, plain, (![B_109, B_96]: (v5_relat_1(B_109, B_96) | ~v1_relat_1(B_109) | ~v1_xboole_0(k2_relat_1(B_109)))), inference(resolution, [status(thm)], [c_126, c_160])).
% 6.60/2.39  tff(c_3949, plain, (![B_96]: (v5_relat_1('#skF_8', B_96) | ~v1_relat_1('#skF_8') | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3943, c_169])).
% 6.60/2.39  tff(c_3961, plain, (![B_96]: (v5_relat_1('#skF_8', B_96))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_116, c_3949])).
% 6.60/2.39  tff(c_3903, plain, (v1_xboole_0(k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_218])).
% 6.60/2.39  tff(c_3907, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_3903, c_81])).
% 6.60/2.39  tff(c_3910, plain, (k1_relset_1('#skF_7', '#skF_5', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3907, c_185])).
% 6.60/2.39  tff(c_4463, plain, (![B_516, C_517, A_518]: (k1_xboole_0=B_516 | v1_funct_2(C_517, A_518, B_516) | k1_relset_1(A_518, B_516, C_517)!=A_518 | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(A_518, B_516))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.60/2.39  tff(c_4470, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_9', '#skF_7', '#skF_5') | k1_relset_1('#skF_7', '#skF_5', '#skF_9')!='#skF_7'), inference(resolution, [status(thm)], [c_64, c_4463])).
% 6.60/2.39  tff(c_4476, plain, (k1_xboole_0='#skF_5' | v1_funct_2('#skF_9', '#skF_7', '#skF_5') | k1_xboole_0!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3910, c_4470])).
% 6.60/2.39  tff(c_4479, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_4476])).
% 6.60/2.39  tff(c_4608, plain, (![B_539, A_540, C_541]: (k1_xboole_0=B_539 | k1_relset_1(A_540, B_539, C_541)=A_540 | ~v1_funct_2(C_541, A_540, B_539) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(A_540, B_539))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.60/2.39  tff(c_4618, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_4608])).
% 6.60/2.39  tff(c_4625, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_186, c_4618])).
% 6.60/2.39  tff(c_4626, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_4479, c_4625])).
% 6.60/2.39  tff(c_4724, plain, (![A_548, B_549, C_550]: (k7_partfun1(A_548, B_549, C_550)=k1_funct_1(B_549, C_550) | ~r2_hidden(C_550, k1_relat_1(B_549)) | ~v1_funct_1(B_549) | ~v5_relat_1(B_549, A_548) | ~v1_relat_1(B_549))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.60/2.39  tff(c_4726, plain, (![A_548, C_550]: (k7_partfun1(A_548, '#skF_8', C_550)=k1_funct_1('#skF_8', C_550) | ~r2_hidden(C_550, '#skF_6') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_548) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4626, c_4724])).
% 6.60/2.39  tff(c_4770, plain, (![A_552, C_553]: (k7_partfun1(A_552, '#skF_8', C_553)=k1_funct_1('#skF_8', C_553) | ~r2_hidden(C_553, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_3961, c_72, c_4726])).
% 6.60/2.39  tff(c_4805, plain, (![A_552]: (k7_partfun1(A_552, '#skF_8', '#skF_1'('#skF_6'))=k1_funct_1('#skF_8', '#skF_1'('#skF_6')) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_4770])).
% 6.60/2.39  tff(c_4816, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_4805])).
% 6.60/2.39  tff(c_4819, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_4816, c_81])).
% 6.60/2.39  tff(c_4823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4819])).
% 6.60/2.39  tff(c_4825, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_4805])).
% 6.60/2.39  tff(c_4627, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4626, c_186])).
% 6.60/2.39  tff(c_5042, plain, (![A_578, B_579, C_580]: (r2_hidden('#skF_4'(A_578, B_579, C_580), k2_relset_1(A_578, B_579, C_580)) | k1_relset_1(A_578, B_579, C_580)=k1_xboole_0 | ~m1_subset_1(C_580, k1_zfmisc_1(k2_zfmisc_1(A_578, B_579))) | v1_xboole_0(B_579) | v1_xboole_0(A_578))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.60/2.39  tff(c_5056, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_7', '#skF_8'), k1_xboole_0) | k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_7') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3919, c_5042])).
% 6.60/2.39  tff(c_5063, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_7', '#skF_8'), k1_xboole_0) | k1_xboole_0='#skF_6' | v1_xboole_0('#skF_7') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4627, c_5056])).
% 6.60/2.39  tff(c_5064, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_7', '#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_4825, c_74, c_58, c_5063])).
% 6.60/2.39  tff(c_5071, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_5064, c_2])).
% 6.60/2.39  tff(c_5079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_5071])).
% 6.60/2.39  tff(c_5081, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_4476])).
% 6.60/2.39  tff(c_5110, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5081, c_12])).
% 6.60/2.39  tff(c_5113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_5110])).
% 6.60/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.39  
% 6.60/2.39  Inference rules
% 6.60/2.39  ----------------------
% 6.60/2.39  #Ref     : 0
% 6.60/2.39  #Sup     : 1060
% 6.60/2.39  #Fact    : 0
% 6.60/2.39  #Define  : 0
% 6.60/2.39  #Split   : 35
% 6.60/2.39  #Chain   : 0
% 6.60/2.39  #Close   : 0
% 6.60/2.39  
% 6.60/2.39  Ordering : KBO
% 6.60/2.39  
% 6.60/2.39  Simplification rules
% 6.60/2.39  ----------------------
% 6.60/2.39  #Subsume      : 302
% 6.60/2.39  #Demod        : 542
% 6.60/2.39  #Tautology    : 216
% 6.60/2.39  #SimpNegUnit  : 111
% 6.60/2.39  #BackRed      : 144
% 6.60/2.39  
% 6.60/2.39  #Partial instantiations: 0
% 6.60/2.39  #Strategies tried      : 1
% 6.60/2.39  
% 6.60/2.39  Timing (in seconds)
% 6.60/2.39  ----------------------
% 6.60/2.39  Preprocessing        : 0.39
% 6.60/2.39  Parsing              : 0.18
% 6.60/2.39  CNF conversion       : 0.04
% 6.60/2.39  Main loop            : 1.15
% 6.60/2.39  Inferencing          : 0.39
% 6.60/2.39  Reduction            : 0.36
% 6.60/2.39  Demodulation         : 0.24
% 6.60/2.39  BG Simplification    : 0.05
% 6.60/2.39  Subsumption          : 0.25
% 6.60/2.39  Abstraction          : 0.05
% 6.60/2.39  MUC search           : 0.00
% 6.60/2.39  Cooper               : 0.00
% 6.60/2.39  Total                : 1.58
% 6.60/2.39  Index Insertion      : 0.00
% 6.60/2.39  Index Deletion       : 0.00
% 6.60/2.39  Index Matching       : 0.00
% 6.60/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
