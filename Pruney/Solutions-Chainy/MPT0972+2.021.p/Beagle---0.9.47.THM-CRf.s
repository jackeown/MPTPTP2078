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
% DateTime   : Thu Dec  3 10:11:37 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 361 expanded)
%              Number of leaves         :   36 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 (1119 expanded)
%              Number of equality atoms :   60 ( 274 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1286,plain,(
    ! [A_216,B_217,D_218] :
      ( r2_relset_1(A_216,B_217,D_218,D_218)
      | ~ m1_subset_1(D_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1306,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1286])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_108,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_124,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_108])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1503,plain,(
    ! [A_237,B_238,C_239] :
      ( k1_relset_1(A_237,B_238,C_239) = k1_relat_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1536,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1503])).

tff(c_2254,plain,(
    ! [B_287,A_288,C_289] :
      ( k1_xboole_0 = B_287
      | k1_relset_1(A_288,B_287,C_289) = A_288
      | ~ v1_funct_2(C_289,A_288,B_287)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2272,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_2254])).

tff(c_2291,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1536,c_2272])).

tff(c_2301,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2291])).

tff(c_123,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_108])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1535,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1503])).

tff(c_2269,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_2254])).

tff(c_2288,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1535,c_2269])).

tff(c_2295,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2288])).

tff(c_2695,plain,(
    ! [A_325,B_326] :
      ( r2_hidden('#skF_3'(A_325,B_326),k1_relat_1(A_325))
      | B_326 = A_325
      | k1_relat_1(B_326) != k1_relat_1(A_325)
      | ~ v1_funct_1(B_326)
      | ~ v1_relat_1(B_326)
      | ~ v1_funct_1(A_325)
      | ~ v1_relat_1(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2708,plain,(
    ! [B_326] :
      ( r2_hidden('#skF_3'('#skF_6',B_326),'#skF_4')
      | B_326 = '#skF_6'
      | k1_relat_1(B_326) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_326)
      | ~ v1_relat_1(B_326)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2295,c_2695])).

tff(c_3421,plain,(
    ! [B_387] :
      ( r2_hidden('#skF_3'('#skF_6',B_387),'#skF_4')
      | B_387 = '#skF_6'
      | k1_relat_1(B_387) != '#skF_4'
      | ~ v1_funct_1(B_387)
      | ~ v1_relat_1(B_387) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_2295,c_2708])).

tff(c_58,plain,(
    ! [E_45] :
      ( k1_funct_1('#skF_7',E_45) = k1_funct_1('#skF_6',E_45)
      | ~ r2_hidden(E_45,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3476,plain,(
    ! [B_390] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_390)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_390))
      | B_390 = '#skF_6'
      | k1_relat_1(B_390) != '#skF_4'
      | ~ v1_funct_1(B_390)
      | ~ v1_relat_1(B_390) ) ),
    inference(resolution,[status(thm)],[c_3421,c_58])).

tff(c_32,plain,(
    ! [B_26,A_22] :
      ( k1_funct_1(B_26,'#skF_3'(A_22,B_26)) != k1_funct_1(A_22,'#skF_3'(A_22,B_26))
      | B_26 = A_22
      | k1_relat_1(B_26) != k1_relat_1(A_22)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3483,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3476,c_32])).

tff(c_3490,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_64,c_2301,c_123,c_70,c_2295,c_2301,c_3483])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3514,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3490,c_56])).

tff(c_3525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_3514])).

tff(c_3526,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2291])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3564,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3526,c_12])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3563,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3526,c_3526,c_22])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1177,plain,(
    ! [C_202,A_203,B_204] :
      ( r2_hidden(C_202,A_203)
      | ~ r2_hidden(C_202,B_204)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1242,plain,(
    ! [A_212,A_213] :
      ( r2_hidden('#skF_1'(A_212),A_213)
      | ~ m1_subset_1(A_212,k1_zfmisc_1(A_213))
      | v1_xboole_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_4,c_1177])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1262,plain,(
    ! [A_214,A_215] :
      ( ~ v1_xboole_0(A_214)
      | ~ m1_subset_1(A_215,k1_zfmisc_1(A_214))
      | v1_xboole_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_1242,c_2])).

tff(c_1283,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1262])).

tff(c_1310,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1283])).

tff(c_3607,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3563,c_1310])).

tff(c_3614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3564,c_3607])).

tff(c_3615,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2288])).

tff(c_3653,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_12])).

tff(c_3652,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_3615,c_22])).

tff(c_3696,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3652,c_1310])).

tff(c_3703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3653,c_3696])).

tff(c_3704,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_3705,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_158,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_158,c_2])).

tff(c_174,plain,(
    ! [A_67,B_68] :
      ( ~ v1_xboole_0(A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_158,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_178,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_174,c_14])).

tff(c_185,plain,(
    ! [B_66,A_65] :
      ( B_66 = A_65
      | ~ v1_xboole_0(B_66)
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_173,c_178])).

tff(c_3737,plain,(
    ! [A_403] :
      ( A_403 = '#skF_7'
      | ~ v1_xboole_0(A_403) ) ),
    inference(resolution,[status(thm)],[c_3704,c_185])).

tff(c_3744,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3705,c_3737])).

tff(c_3759,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3744,c_66])).

tff(c_1261,plain,(
    ! [A_213,A_212] :
      ( ~ v1_xboole_0(A_213)
      | ~ m1_subset_1(A_212,k1_zfmisc_1(A_213))
      | v1_xboole_0(A_212) ) ),
    inference(resolution,[status(thm)],[c_1242,c_2])).

tff(c_3789,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_3759,c_1261])).

tff(c_3794,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3704,c_3789])).

tff(c_3712,plain,(
    ! [A_65] :
      ( A_65 = '#skF_7'
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_3704,c_185])).

tff(c_3801,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3794,c_3712])).

tff(c_3815,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3801,c_56])).

tff(c_3823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_3815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:51:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.02  
% 5.32/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.02  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.32/2.02  
% 5.32/2.02  %Foreground sorts:
% 5.32/2.02  
% 5.32/2.02  
% 5.32/2.02  %Background operators:
% 5.32/2.02  
% 5.32/2.02  
% 5.32/2.02  %Foreground operators:
% 5.32/2.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.32/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.02  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.32/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.32/2.02  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.32/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.32/2.02  tff('#skF_7', type, '#skF_7': $i).
% 5.32/2.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.32/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.32/2.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.32/2.02  tff('#skF_6', type, '#skF_6': $i).
% 5.32/2.02  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.32/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.02  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.32/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.32/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.32/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.32/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.32/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.32/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.32/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.02  
% 5.32/2.04  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 5.32/2.04  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.32/2.04  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.32/2.04  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.32/2.04  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.32/2.04  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.32/2.04  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.32/2.04  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.32/2.04  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.32/2.04  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.32/2.04  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.32/2.04  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.32/2.04  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.32/2.04  tff(c_1286, plain, (![A_216, B_217, D_218]: (r2_relset_1(A_216, B_217, D_218, D_218) | ~m1_subset_1(D_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.32/2.04  tff(c_1306, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_1286])).
% 5.32/2.04  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.32/2.04  tff(c_108, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.32/2.04  tff(c_124, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_108])).
% 5.32/2.04  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.32/2.04  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.32/2.04  tff(c_1503, plain, (![A_237, B_238, C_239]: (k1_relset_1(A_237, B_238, C_239)=k1_relat_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.32/2.04  tff(c_1536, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_1503])).
% 5.32/2.04  tff(c_2254, plain, (![B_287, A_288, C_289]: (k1_xboole_0=B_287 | k1_relset_1(A_288, B_287, C_289)=A_288 | ~v1_funct_2(C_289, A_288, B_287) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.32/2.04  tff(c_2272, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_2254])).
% 5.32/2.04  tff(c_2291, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1536, c_2272])).
% 5.32/2.04  tff(c_2301, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_2291])).
% 5.32/2.04  tff(c_123, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_108])).
% 5.32/2.04  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.32/2.04  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.32/2.04  tff(c_1535, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_1503])).
% 5.32/2.04  tff(c_2269, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_2254])).
% 5.32/2.04  tff(c_2288, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1535, c_2269])).
% 5.32/2.04  tff(c_2295, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2288])).
% 5.32/2.04  tff(c_2695, plain, (![A_325, B_326]: (r2_hidden('#skF_3'(A_325, B_326), k1_relat_1(A_325)) | B_326=A_325 | k1_relat_1(B_326)!=k1_relat_1(A_325) | ~v1_funct_1(B_326) | ~v1_relat_1(B_326) | ~v1_funct_1(A_325) | ~v1_relat_1(A_325))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.32/2.04  tff(c_2708, plain, (![B_326]: (r2_hidden('#skF_3'('#skF_6', B_326), '#skF_4') | B_326='#skF_6' | k1_relat_1(B_326)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_326) | ~v1_relat_1(B_326) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2295, c_2695])).
% 5.32/2.04  tff(c_3421, plain, (![B_387]: (r2_hidden('#skF_3'('#skF_6', B_387), '#skF_4') | B_387='#skF_6' | k1_relat_1(B_387)!='#skF_4' | ~v1_funct_1(B_387) | ~v1_relat_1(B_387))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_2295, c_2708])).
% 5.32/2.04  tff(c_58, plain, (![E_45]: (k1_funct_1('#skF_7', E_45)=k1_funct_1('#skF_6', E_45) | ~r2_hidden(E_45, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.32/2.04  tff(c_3476, plain, (![B_390]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_390))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_390)) | B_390='#skF_6' | k1_relat_1(B_390)!='#skF_4' | ~v1_funct_1(B_390) | ~v1_relat_1(B_390))), inference(resolution, [status(thm)], [c_3421, c_58])).
% 5.32/2.04  tff(c_32, plain, (![B_26, A_22]: (k1_funct_1(B_26, '#skF_3'(A_22, B_26))!=k1_funct_1(A_22, '#skF_3'(A_22, B_26)) | B_26=A_22 | k1_relat_1(B_26)!=k1_relat_1(A_22) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.32/2.04  tff(c_3483, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3476, c_32])).
% 5.32/2.04  tff(c_3490, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_64, c_2301, c_123, c_70, c_2295, c_2301, c_3483])).
% 5.32/2.04  tff(c_56, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.32/2.04  tff(c_3514, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3490, c_56])).
% 5.32/2.04  tff(c_3525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1306, c_3514])).
% 5.32/2.04  tff(c_3526, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2291])).
% 5.32/2.04  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.32/2.04  tff(c_3564, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3526, c_12])).
% 5.32/2.04  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.32/2.04  tff(c_3563, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3526, c_3526, c_22])).
% 5.32/2.04  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.04  tff(c_1177, plain, (![C_202, A_203, B_204]: (r2_hidden(C_202, A_203) | ~r2_hidden(C_202, B_204) | ~m1_subset_1(B_204, k1_zfmisc_1(A_203)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.32/2.04  tff(c_1242, plain, (![A_212, A_213]: (r2_hidden('#skF_1'(A_212), A_213) | ~m1_subset_1(A_212, k1_zfmisc_1(A_213)) | v1_xboole_0(A_212))), inference(resolution, [status(thm)], [c_4, c_1177])).
% 5.32/2.04  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.04  tff(c_1262, plain, (![A_214, A_215]: (~v1_xboole_0(A_214) | ~m1_subset_1(A_215, k1_zfmisc_1(A_214)) | v1_xboole_0(A_215))), inference(resolution, [status(thm)], [c_1242, c_2])).
% 5.32/2.04  tff(c_1283, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_1262])).
% 5.32/2.04  tff(c_1310, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1283])).
% 5.32/2.04  tff(c_3607, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3563, c_1310])).
% 5.32/2.04  tff(c_3614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3564, c_3607])).
% 5.32/2.04  tff(c_3615, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2288])).
% 5.32/2.04  tff(c_3653, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_12])).
% 5.32/2.04  tff(c_3652, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_3615, c_22])).
% 5.32/2.04  tff(c_3696, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3652, c_1310])).
% 5.32/2.04  tff(c_3703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3653, c_3696])).
% 5.32/2.04  tff(c_3704, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1283])).
% 5.32/2.04  tff(c_3705, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1283])).
% 5.32/2.04  tff(c_158, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.32/2.04  tff(c_173, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_158, c_2])).
% 5.32/2.04  tff(c_174, plain, (![A_67, B_68]: (~v1_xboole_0(A_67) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_158, c_2])).
% 5.32/2.04  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.32/2.04  tff(c_178, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_174, c_14])).
% 5.32/2.04  tff(c_185, plain, (![B_66, A_65]: (B_66=A_65 | ~v1_xboole_0(B_66) | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_173, c_178])).
% 5.32/2.04  tff(c_3737, plain, (![A_403]: (A_403='#skF_7' | ~v1_xboole_0(A_403))), inference(resolution, [status(thm)], [c_3704, c_185])).
% 5.32/2.04  tff(c_3744, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_3705, c_3737])).
% 5.32/2.04  tff(c_3759, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3744, c_66])).
% 5.32/2.04  tff(c_1261, plain, (![A_213, A_212]: (~v1_xboole_0(A_213) | ~m1_subset_1(A_212, k1_zfmisc_1(A_213)) | v1_xboole_0(A_212))), inference(resolution, [status(thm)], [c_1242, c_2])).
% 5.32/2.04  tff(c_3789, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_3759, c_1261])).
% 5.32/2.04  tff(c_3794, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3704, c_3789])).
% 5.32/2.04  tff(c_3712, plain, (![A_65]: (A_65='#skF_7' | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_3704, c_185])).
% 5.32/2.04  tff(c_3801, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_3794, c_3712])).
% 5.32/2.04  tff(c_3815, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3801, c_56])).
% 5.32/2.04  tff(c_3823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1306, c_3815])).
% 5.32/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.04  
% 5.32/2.04  Inference rules
% 5.32/2.04  ----------------------
% 5.32/2.04  #Ref     : 1
% 5.32/2.04  #Sup     : 773
% 5.32/2.04  #Fact    : 0
% 5.32/2.04  #Define  : 0
% 5.32/2.04  #Split   : 21
% 5.32/2.04  #Chain   : 0
% 5.32/2.04  #Close   : 0
% 5.32/2.04  
% 5.32/2.04  Ordering : KBO
% 5.32/2.04  
% 5.32/2.04  Simplification rules
% 5.32/2.04  ----------------------
% 5.32/2.04  #Subsume      : 262
% 5.32/2.04  #Demod        : 594
% 5.32/2.04  #Tautology    : 301
% 5.32/2.04  #SimpNegUnit  : 96
% 5.32/2.04  #BackRed      : 247
% 5.32/2.04  
% 5.32/2.04  #Partial instantiations: 0
% 5.32/2.04  #Strategies tried      : 1
% 5.32/2.04  
% 5.32/2.04  Timing (in seconds)
% 5.32/2.04  ----------------------
% 5.32/2.04  Preprocessing        : 0.34
% 5.32/2.04  Parsing              : 0.18
% 5.32/2.04  CNF conversion       : 0.02
% 5.32/2.04  Main loop            : 0.89
% 5.32/2.04  Inferencing          : 0.29
% 5.32/2.04  Reduction            : 0.27
% 5.32/2.04  Demodulation         : 0.18
% 5.32/2.04  BG Simplification    : 0.04
% 5.32/2.04  Subsumption          : 0.21
% 5.32/2.04  Abstraction          : 0.04
% 5.32/2.04  MUC search           : 0.00
% 5.32/2.04  Cooper               : 0.00
% 5.32/2.04  Total                : 1.26
% 5.32/2.04  Index Insertion      : 0.00
% 5.32/2.04  Index Deletion       : 0.00
% 5.32/2.04  Index Matching       : 0.00
% 5.32/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
