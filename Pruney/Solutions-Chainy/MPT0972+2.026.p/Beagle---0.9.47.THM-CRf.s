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
% DateTime   : Thu Dec  3 10:11:38 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :  200 (1337 expanded)
%              Number of leaves         :   35 ( 444 expanded)
%              Depth                    :   16
%              Number of atoms          :  372 (4018 expanded)
%              Number of equality atoms :  144 (1104 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_129,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_74,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_377,plain,(
    ! [A_90,B_91,D_92] :
      ( r2_relset_1(A_90,B_91,D_92,D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_390,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_377])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_120,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_137,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_120])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_392,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_411,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_392])).

tff(c_582,plain,(
    ! [B_133,A_134,C_135] :
      ( k1_xboole_0 = B_133
      | k1_relset_1(A_134,B_133,C_135) = A_134
      | ~ v1_funct_2(C_135,A_134,B_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_592,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_582])).

tff(c_605,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_411,c_592])).

tff(c_613,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_605])).

tff(c_136,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_120])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_410,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_392])).

tff(c_589,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_582])).

tff(c_602,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_410,c_589])).

tff(c_607,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_602])).

tff(c_738,plain,(
    ! [A_154,B_155] :
      ( r2_hidden('#skF_2'(A_154,B_155),k1_relat_1(A_154))
      | B_155 = A_154
      | k1_relat_1(B_155) != k1_relat_1(A_154)
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_748,plain,(
    ! [B_155] :
      ( r2_hidden('#skF_2'('#skF_6',B_155),'#skF_3')
      | B_155 = '#skF_6'
      | k1_relat_1(B_155) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_738])).

tff(c_1103,plain,(
    ! [B_192] :
      ( r2_hidden('#skF_2'('#skF_6',B_192),'#skF_3')
      | B_192 = '#skF_6'
      | k1_relat_1(B_192) != '#skF_3'
      | ~ v1_funct_1(B_192)
      | ~ v1_relat_1(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_60,c_607,c_748])).

tff(c_54,plain,(
    ! [E_38] :
      ( k1_funct_1('#skF_5',E_38) = k1_funct_1('#skF_6',E_38)
      | ~ r2_hidden(E_38,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1413,plain,(
    ! [B_211] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_211)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_211))
      | B_211 = '#skF_6'
      | k1_relat_1(B_211) != '#skF_3'
      | ~ v1_funct_1(B_211)
      | ~ v1_relat_1(B_211) ) ),
    inference(resolution,[status(thm)],[c_1103,c_54])).

tff(c_28,plain,(
    ! [B_19,A_15] :
      ( k1_funct_1(B_19,'#skF_2'(A_15,B_19)) != k1_funct_1(A_15,'#skF_2'(A_15,B_19))
      | B_19 = A_15
      | k1_relat_1(B_19) != k1_relat_1(A_15)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1420,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_28])).

tff(c_1427,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_66,c_613,c_136,c_60,c_613,c_607,c_1420])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1448,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_52])).

tff(c_1459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_1448])).

tff(c_1460,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_31,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_69,plain,(
    ! [A_31] :
      ( v1_funct_2(k1_xboole_0,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_40])).

tff(c_298,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_301,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_298])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_301])).

tff(c_307,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_309,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_307,c_26])).

tff(c_323,plain,(
    ! [A_86] : ~ r2_hidden(A_86,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_309])).

tff(c_328,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_1479,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_328])).

tff(c_1488,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_1460,c_18])).

tff(c_95,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_95])).

tff(c_171,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_102,c_171])).

tff(c_329,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_1583,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_329])).

tff(c_1592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1583])).

tff(c_1593,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_602])).

tff(c_1612,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_328])).

tff(c_1621,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_1593,c_18])).

tff(c_1671,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1621,c_329])).

tff(c_1680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_1671])).

tff(c_1681,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_213,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_221,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_213])).

tff(c_223,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_1709,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_223])).

tff(c_1713,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_62])).

tff(c_1847,plain,(
    ! [A_236,B_237,C_238] :
      ( k1_relset_1(A_236,B_237,C_238) = k1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1941,plain,(
    ! [C_256] :
      ( k1_relset_1('#skF_3','#skF_4',C_256) = k1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1681,c_1847])).

tff(c_1952,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1713,c_1941])).

tff(c_2236,plain,(
    ! [B_304,C_305,A_306] :
      ( k1_xboole_0 = B_304
      | v1_funct_2(C_305,A_306,B_304)
      | k1_relset_1(A_306,B_304,C_305) != A_306
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2239,plain,(
    ! [C_305] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(C_305,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_305) != '#skF_3'
      | ~ m1_subset_1(C_305,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1681,c_2236])).

tff(c_2360,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2239])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1724,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1681,c_16])).

tff(c_1828,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1724])).

tff(c_2380,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_1828])).

tff(c_2392,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_2360,c_18])).

tff(c_2515,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_1681])).

tff(c_2517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2380,c_2515])).

tff(c_2519,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2239])).

tff(c_2331,plain,(
    ! [B_316,A_317,C_318] :
      ( k1_xboole_0 = B_316
      | k1_relset_1(A_317,B_316,C_318) = A_317
      | ~ v1_funct_2(C_318,A_317,B_316)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_317,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2334,plain,(
    ! [C_318] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_318) = '#skF_3'
      | ~ v1_funct_2(C_318,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_318,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1681,c_2331])).

tff(c_2578,plain,(
    ! [C_333] :
      ( k1_relset_1('#skF_3','#skF_4',C_333) = '#skF_3'
      | ~ v1_funct_2(C_333,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_333,k1_zfmisc_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2519,c_2334])).

tff(c_2581,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1713,c_2578])).

tff(c_2591,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1952,c_2581])).

tff(c_1712,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_56])).

tff(c_1953,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1712,c_1941])).

tff(c_2584,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1712,c_2578])).

tff(c_2594,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1953,c_2584])).

tff(c_2665,plain,(
    ! [A_338,B_339] :
      ( r2_hidden('#skF_2'(A_338,B_339),k1_relat_1(A_338))
      | B_339 = A_338
      | k1_relat_1(B_339) != k1_relat_1(A_338)
      | ~ v1_funct_1(B_339)
      | ~ v1_relat_1(B_339)
      | ~ v1_funct_1(A_338)
      | ~ v1_relat_1(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2672,plain,(
    ! [B_339] :
      ( r2_hidden('#skF_2'('#skF_6',B_339),'#skF_3')
      | B_339 = '#skF_6'
      | k1_relat_1(B_339) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_339)
      | ~ v1_relat_1(B_339)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2594,c_2665])).

tff(c_2759,plain,(
    ! [B_347] :
      ( r2_hidden('#skF_2'('#skF_6',B_347),'#skF_3')
      | B_347 = '#skF_6'
      | k1_relat_1(B_347) != '#skF_3'
      | ~ v1_funct_1(B_347)
      | ~ v1_relat_1(B_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_60,c_2594,c_2672])).

tff(c_2861,plain,(
    ! [B_357] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_357)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_357))
      | B_357 = '#skF_6'
      | k1_relat_1(B_357) != '#skF_3'
      | ~ v1_funct_1(B_357)
      | ~ v1_relat_1(B_357) ) ),
    inference(resolution,[status(thm)],[c_2759,c_54])).

tff(c_2868,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2861,c_28])).

tff(c_2875,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_66,c_2591,c_136,c_60,c_2594,c_2591,c_2868])).

tff(c_103,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_95])).

tff(c_178,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_171])).

tff(c_265,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_1708,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_265])).

tff(c_2888,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_1708])).

tff(c_2902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2888])).

tff(c_2904,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1724])).

tff(c_2917,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2904,c_8])).

tff(c_2921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1709,c_2917])).

tff(c_2922,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2924,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_223])).

tff(c_2928,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_62])).

tff(c_3180,plain,(
    ! [A_389,B_390,C_391] :
      ( k1_relset_1(A_389,B_390,C_391) = k1_relat_1(C_391)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3275,plain,(
    ! [C_410] :
      ( k1_relset_1('#skF_3','#skF_4',C_410) = k1_relat_1(C_410)
      | ~ m1_subset_1(C_410,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2922,c_3180])).

tff(c_3286,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2928,c_3275])).

tff(c_3435,plain,(
    ! [B_430,A_431,C_432] :
      ( k1_xboole_0 = B_430
      | k1_relset_1(A_431,B_430,C_432) = A_431
      | ~ v1_funct_2(C_432,A_431,B_430)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_431,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3438,plain,(
    ! [C_432] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1('#skF_3','#skF_4',C_432) = '#skF_3'
      | ~ v1_funct_2(C_432,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_432,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2922,c_3435])).

tff(c_3777,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3438])).

tff(c_2939,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2922,c_16])).

tff(c_3072,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2939])).

tff(c_3798,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3777,c_3072])).

tff(c_3810,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3777,c_3777,c_18])).

tff(c_3957,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3810,c_2922])).

tff(c_3959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3798,c_3957])).

tff(c_3962,plain,(
    ! [C_479] :
      ( k1_relset_1('#skF_3','#skF_4',C_479) = '#skF_3'
      | ~ v1_funct_2(C_479,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_479,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_3438])).

tff(c_3965,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2928,c_3962])).

tff(c_3975,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3286,c_3965])).

tff(c_2927,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_56])).

tff(c_3287,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2927,c_3275])).

tff(c_3968,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2927,c_3962])).

tff(c_3978,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3287,c_3968])).

tff(c_30,plain,(
    ! [A_15,B_19] :
      ( r2_hidden('#skF_2'(A_15,B_19),k1_relat_1(A_15))
      | B_19 = A_15
      | k1_relat_1(B_19) != k1_relat_1(A_15)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4001,plain,(
    ! [B_19] :
      ( r2_hidden('#skF_2'('#skF_6',B_19),'#skF_3')
      | B_19 = '#skF_6'
      | k1_relat_1(B_19) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3978,c_30])).

tff(c_4033,plain,(
    ! [B_483] :
      ( r2_hidden('#skF_2'('#skF_6',B_483),'#skF_3')
      | B_483 = '#skF_6'
      | k1_relat_1(B_483) != '#skF_3'
      | ~ v1_funct_1(B_483)
      | ~ v1_relat_1(B_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_60,c_3978,c_4001])).

tff(c_4078,plain,(
    ! [B_488] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_488)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_488))
      | B_488 = '#skF_6'
      | k1_relat_1(B_488) != '#skF_3'
      | ~ v1_funct_1(B_488)
      | ~ v1_relat_1(B_488) ) ),
    inference(resolution,[status(thm)],[c_4033,c_54])).

tff(c_4085,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4078,c_28])).

tff(c_4092,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_66,c_3975,c_136,c_60,c_3978,c_3975,c_4085])).

tff(c_2926,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_102])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2949,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2926,c_10])).

tff(c_3043,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2949])).

tff(c_4119,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4092,c_3043])).

tff(c_4136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4119])).

tff(c_4138,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2939])).

tff(c_4151,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4138,c_8])).

tff(c_4155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2924,c_4151])).

tff(c_4156,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2949])).

tff(c_4166,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4156,c_52])).

tff(c_4159,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4156,c_2927])).

tff(c_4162,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4156,c_2922])).

tff(c_36,plain,(
    ! [A_27,B_28,D_30] :
      ( r2_relset_1(A_27,B_28,D_30,D_30)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4307,plain,(
    ! [D_513] :
      ( r2_relset_1('#skF_3','#skF_4',D_513,D_513)
      | ~ m1_subset_1(D_513,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4162,c_36])).

tff(c_4309,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_4159,c_4307])).

tff(c_4316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4166,c_4309])).

tff(c_4347,plain,(
    ! [A_516] : ~ r2_hidden(A_516,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_4352,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4347])).

tff(c_4318,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_222,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_68,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_213])).

tff(c_4319,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_4344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4318,c_4319])).

tff(c_4357,plain,(
    ! [A_520] : ~ r2_hidden(A_520,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_4381,plain,(
    ! [B_522] : r1_tarski('#skF_5',B_522) ),
    inference(resolution,[status(thm)],[c_6,c_4357])).

tff(c_4398,plain,(
    ! [B_523] :
      ( B_523 = '#skF_5'
      | ~ r1_tarski(B_523,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4381,c_10])).

tff(c_4413,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4352,c_4398])).

tff(c_4423,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4413,c_52])).

tff(c_4589,plain,(
    ! [A_532,B_533,D_534] :
      ( r2_relset_1(A_532,B_533,D_534,D_534)
      | ~ m1_subset_1(D_534,k1_zfmisc_1(k2_zfmisc_1(A_532,B_533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4598,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_4589])).

tff(c_4603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4423,c_4598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.11  
% 5.81/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.12  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.81/2.12  
% 5.81/2.12  %Foreground sorts:
% 5.81/2.12  
% 5.81/2.12  
% 5.81/2.12  %Background operators:
% 5.81/2.12  
% 5.81/2.12  
% 5.81/2.12  %Foreground operators:
% 5.81/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.81/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.12  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.81/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.81/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.81/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.81/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.81/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.81/2.12  tff('#skF_6', type, '#skF_6': $i).
% 5.81/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.81/2.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.81/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.81/2.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.81/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.81/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.81/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.81/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.81/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.81/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.81/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.81/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.81/2.12  
% 5.81/2.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.81/2.15  tff(f_129, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 5.81/2.15  tff(f_90, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.81/2.15  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.81/2.15  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.81/2.15  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.81/2.15  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.81/2.15  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.81/2.15  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.81/2.15  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.81/2.15  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.81/2.15  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.81/2.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.81/2.15  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.81/2.15  tff(c_377, plain, (![A_90, B_91, D_92]: (r2_relset_1(A_90, B_91, D_92, D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.81/2.15  tff(c_390, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_377])).
% 5.81/2.15  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.81/2.15  tff(c_120, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.81/2.15  tff(c_137, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_120])).
% 5.81/2.15  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.81/2.15  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.81/2.15  tff(c_392, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.81/2.15  tff(c_411, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_392])).
% 5.81/2.15  tff(c_582, plain, (![B_133, A_134, C_135]: (k1_xboole_0=B_133 | k1_relset_1(A_134, B_133, C_135)=A_134 | ~v1_funct_2(C_135, A_134, B_133) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.81/2.15  tff(c_592, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_582])).
% 5.81/2.15  tff(c_605, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_411, c_592])).
% 5.81/2.15  tff(c_613, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_605])).
% 5.81/2.15  tff(c_136, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_120])).
% 5.81/2.15  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.81/2.15  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.81/2.15  tff(c_410, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_392])).
% 5.81/2.15  tff(c_589, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_582])).
% 5.81/2.15  tff(c_602, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_410, c_589])).
% 5.81/2.15  tff(c_607, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_602])).
% 5.81/2.15  tff(c_738, plain, (![A_154, B_155]: (r2_hidden('#skF_2'(A_154, B_155), k1_relat_1(A_154)) | B_155=A_154 | k1_relat_1(B_155)!=k1_relat_1(A_154) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.81/2.15  tff(c_748, plain, (![B_155]: (r2_hidden('#skF_2'('#skF_6', B_155), '#skF_3') | B_155='#skF_6' | k1_relat_1(B_155)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_155) | ~v1_relat_1(B_155) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_738])).
% 5.81/2.15  tff(c_1103, plain, (![B_192]: (r2_hidden('#skF_2'('#skF_6', B_192), '#skF_3') | B_192='#skF_6' | k1_relat_1(B_192)!='#skF_3' | ~v1_funct_1(B_192) | ~v1_relat_1(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_60, c_607, c_748])).
% 5.81/2.15  tff(c_54, plain, (![E_38]: (k1_funct_1('#skF_5', E_38)=k1_funct_1('#skF_6', E_38) | ~r2_hidden(E_38, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.81/2.15  tff(c_1413, plain, (![B_211]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_211))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_211)) | B_211='#skF_6' | k1_relat_1(B_211)!='#skF_3' | ~v1_funct_1(B_211) | ~v1_relat_1(B_211))), inference(resolution, [status(thm)], [c_1103, c_54])).
% 5.81/2.15  tff(c_28, plain, (![B_19, A_15]: (k1_funct_1(B_19, '#skF_2'(A_15, B_19))!=k1_funct_1(A_15, '#skF_2'(A_15, B_19)) | B_19=A_15 | k1_relat_1(B_19)!=k1_relat_1(A_15) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.81/2.15  tff(c_1420, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1413, c_28])).
% 5.81/2.15  tff(c_1427, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_66, c_613, c_136, c_60, c_613, c_607, c_1420])).
% 5.81/2.15  tff(c_52, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.81/2.15  tff(c_1448, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_52])).
% 5.81/2.15  tff(c_1459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_390, c_1448])).
% 5.81/2.15  tff(c_1460, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_605])).
% 5.81/2.15  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.81/2.15  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.81/2.15  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.81/2.15  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.15  tff(c_40, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_31, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.81/2.15  tff(c_69, plain, (![A_31]: (v1_funct_2(k1_xboole_0, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_40])).
% 5.81/2.15  tff(c_298, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_69])).
% 5.81/2.15  tff(c_301, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_298])).
% 5.81/2.15  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_301])).
% 5.81/2.15  tff(c_307, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_69])).
% 5.81/2.15  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.81/2.15  tff(c_309, plain, (![A_12]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_307, c_26])).
% 5.81/2.15  tff(c_323, plain, (![A_86]: (~r2_hidden(A_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_309])).
% 5.81/2.15  tff(c_328, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_323])).
% 5.81/2.15  tff(c_1479, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1460, c_328])).
% 5.81/2.15  tff(c_1488, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1460, c_1460, c_18])).
% 5.81/2.15  tff(c_95, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.81/2.15  tff(c_102, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_95])).
% 5.81/2.15  tff(c_171, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.81/2.15  tff(c_179, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_102, c_171])).
% 5.81/2.15  tff(c_329, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_179])).
% 5.81/2.15  tff(c_1583, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_329])).
% 5.81/2.15  tff(c_1592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1583])).
% 5.81/2.15  tff(c_1593, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_602])).
% 5.81/2.15  tff(c_1612, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_328])).
% 5.81/2.15  tff(c_1621, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_1593, c_18])).
% 5.81/2.15  tff(c_1671, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1621, c_329])).
% 5.81/2.15  tff(c_1680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1612, c_1671])).
% 5.81/2.15  tff(c_1681, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_179])).
% 5.81/2.15  tff(c_213, plain, (![C_66, B_67, A_68]: (~v1_xboole_0(C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.81/2.15  tff(c_221, plain, (![A_68]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_68, '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_213])).
% 5.81/2.15  tff(c_223, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_221])).
% 5.81/2.15  tff(c_1709, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_223])).
% 5.81/2.15  tff(c_1713, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_62])).
% 5.81/2.15  tff(c_1847, plain, (![A_236, B_237, C_238]: (k1_relset_1(A_236, B_237, C_238)=k1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.81/2.15  tff(c_1941, plain, (![C_256]: (k1_relset_1('#skF_3', '#skF_4', C_256)=k1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1681, c_1847])).
% 5.81/2.15  tff(c_1952, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1713, c_1941])).
% 5.81/2.15  tff(c_2236, plain, (![B_304, C_305, A_306]: (k1_xboole_0=B_304 | v1_funct_2(C_305, A_306, B_304) | k1_relset_1(A_306, B_304, C_305)!=A_306 | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_304))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.81/2.15  tff(c_2239, plain, (![C_305]: (k1_xboole_0='#skF_4' | v1_funct_2(C_305, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_305)!='#skF_3' | ~m1_subset_1(C_305, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1681, c_2236])).
% 5.81/2.15  tff(c_2360, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2239])).
% 5.81/2.15  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.15  tff(c_1724, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1681, c_16])).
% 5.81/2.15  tff(c_1828, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_1724])).
% 5.81/2.15  tff(c_2380, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_1828])).
% 5.81/2.15  tff(c_2392, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_2360, c_18])).
% 5.81/2.15  tff(c_2515, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_1681])).
% 5.81/2.15  tff(c_2517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2380, c_2515])).
% 5.81/2.15  tff(c_2519, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2239])).
% 5.81/2.15  tff(c_2331, plain, (![B_316, A_317, C_318]: (k1_xboole_0=B_316 | k1_relset_1(A_317, B_316, C_318)=A_317 | ~v1_funct_2(C_318, A_317, B_316) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_317, B_316))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.81/2.15  tff(c_2334, plain, (![C_318]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_318)='#skF_3' | ~v1_funct_2(C_318, '#skF_3', '#skF_4') | ~m1_subset_1(C_318, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1681, c_2331])).
% 5.81/2.15  tff(c_2578, plain, (![C_333]: (k1_relset_1('#skF_3', '#skF_4', C_333)='#skF_3' | ~v1_funct_2(C_333, '#skF_3', '#skF_4') | ~m1_subset_1(C_333, k1_zfmisc_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_2519, c_2334])).
% 5.81/2.15  tff(c_2581, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1713, c_2578])).
% 5.81/2.15  tff(c_2591, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1952, c_2581])).
% 5.81/2.15  tff(c_1712, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_56])).
% 5.81/2.15  tff(c_1953, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1712, c_1941])).
% 5.81/2.15  tff(c_2584, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1712, c_2578])).
% 5.81/2.15  tff(c_2594, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1953, c_2584])).
% 5.81/2.15  tff(c_2665, plain, (![A_338, B_339]: (r2_hidden('#skF_2'(A_338, B_339), k1_relat_1(A_338)) | B_339=A_338 | k1_relat_1(B_339)!=k1_relat_1(A_338) | ~v1_funct_1(B_339) | ~v1_relat_1(B_339) | ~v1_funct_1(A_338) | ~v1_relat_1(A_338))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.81/2.15  tff(c_2672, plain, (![B_339]: (r2_hidden('#skF_2'('#skF_6', B_339), '#skF_3') | B_339='#skF_6' | k1_relat_1(B_339)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_339) | ~v1_relat_1(B_339) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2594, c_2665])).
% 5.81/2.15  tff(c_2759, plain, (![B_347]: (r2_hidden('#skF_2'('#skF_6', B_347), '#skF_3') | B_347='#skF_6' | k1_relat_1(B_347)!='#skF_3' | ~v1_funct_1(B_347) | ~v1_relat_1(B_347))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_60, c_2594, c_2672])).
% 5.81/2.15  tff(c_2861, plain, (![B_357]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_357))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_357)) | B_357='#skF_6' | k1_relat_1(B_357)!='#skF_3' | ~v1_funct_1(B_357) | ~v1_relat_1(B_357))), inference(resolution, [status(thm)], [c_2759, c_54])).
% 5.81/2.15  tff(c_2868, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2861, c_28])).
% 5.81/2.15  tff(c_2875, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_66, c_2591, c_136, c_60, c_2594, c_2591, c_2868])).
% 5.81/2.15  tff(c_103, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_95])).
% 5.81/2.15  tff(c_178, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_103, c_171])).
% 5.81/2.15  tff(c_265, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_178])).
% 5.81/2.15  tff(c_1708, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_265])).
% 5.81/2.15  tff(c_2888, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2875, c_1708])).
% 5.81/2.15  tff(c_2902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_2888])).
% 5.81/2.15  tff(c_2904, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1724])).
% 5.81/2.15  tff(c_2917, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2904, c_8])).
% 5.81/2.15  tff(c_2921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1709, c_2917])).
% 5.81/2.15  tff(c_2922, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_178])).
% 5.81/2.15  tff(c_2924, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_223])).
% 5.81/2.15  tff(c_2928, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_62])).
% 5.81/2.15  tff(c_3180, plain, (![A_389, B_390, C_391]: (k1_relset_1(A_389, B_390, C_391)=k1_relat_1(C_391) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.81/2.15  tff(c_3275, plain, (![C_410]: (k1_relset_1('#skF_3', '#skF_4', C_410)=k1_relat_1(C_410) | ~m1_subset_1(C_410, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2922, c_3180])).
% 5.81/2.15  tff(c_3286, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2928, c_3275])).
% 5.81/2.15  tff(c_3435, plain, (![B_430, A_431, C_432]: (k1_xboole_0=B_430 | k1_relset_1(A_431, B_430, C_432)=A_431 | ~v1_funct_2(C_432, A_431, B_430) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_431, B_430))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.81/2.15  tff(c_3438, plain, (![C_432]: (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', C_432)='#skF_3' | ~v1_funct_2(C_432, '#skF_3', '#skF_4') | ~m1_subset_1(C_432, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2922, c_3435])).
% 5.81/2.15  tff(c_3777, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3438])).
% 5.81/2.15  tff(c_2939, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2922, c_16])).
% 5.81/2.15  tff(c_3072, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_2939])).
% 5.81/2.15  tff(c_3798, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3777, c_3072])).
% 5.81/2.15  tff(c_3810, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3777, c_3777, c_18])).
% 5.81/2.15  tff(c_3957, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3810, c_2922])).
% 5.81/2.15  tff(c_3959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3798, c_3957])).
% 5.81/2.15  tff(c_3962, plain, (![C_479]: (k1_relset_1('#skF_3', '#skF_4', C_479)='#skF_3' | ~v1_funct_2(C_479, '#skF_3', '#skF_4') | ~m1_subset_1(C_479, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_3438])).
% 5.81/2.15  tff(c_3965, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2928, c_3962])).
% 5.81/2.15  tff(c_3975, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3286, c_3965])).
% 5.81/2.15  tff(c_2927, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_56])).
% 5.81/2.15  tff(c_3287, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2927, c_3275])).
% 5.81/2.15  tff(c_3968, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2927, c_3962])).
% 5.81/2.15  tff(c_3978, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3287, c_3968])).
% 5.81/2.15  tff(c_30, plain, (![A_15, B_19]: (r2_hidden('#skF_2'(A_15, B_19), k1_relat_1(A_15)) | B_19=A_15 | k1_relat_1(B_19)!=k1_relat_1(A_15) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.81/2.15  tff(c_4001, plain, (![B_19]: (r2_hidden('#skF_2'('#skF_6', B_19), '#skF_3') | B_19='#skF_6' | k1_relat_1(B_19)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3978, c_30])).
% 5.81/2.15  tff(c_4033, plain, (![B_483]: (r2_hidden('#skF_2'('#skF_6', B_483), '#skF_3') | B_483='#skF_6' | k1_relat_1(B_483)!='#skF_3' | ~v1_funct_1(B_483) | ~v1_relat_1(B_483))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_60, c_3978, c_4001])).
% 5.81/2.15  tff(c_4078, plain, (![B_488]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_488))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_488)) | B_488='#skF_6' | k1_relat_1(B_488)!='#skF_3' | ~v1_funct_1(B_488) | ~v1_relat_1(B_488))), inference(resolution, [status(thm)], [c_4033, c_54])).
% 5.81/2.15  tff(c_4085, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4078, c_28])).
% 5.81/2.15  tff(c_4092, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_66, c_3975, c_136, c_60, c_3978, c_3975, c_4085])).
% 5.81/2.15  tff(c_2926, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_102])).
% 5.81/2.15  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.81/2.15  tff(c_2949, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2926, c_10])).
% 5.81/2.15  tff(c_3043, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_2949])).
% 5.81/2.15  tff(c_4119, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4092, c_3043])).
% 5.81/2.15  tff(c_4136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_4119])).
% 5.81/2.15  tff(c_4138, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2939])).
% 5.81/2.15  tff(c_4151, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4138, c_8])).
% 5.81/2.15  tff(c_4155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2924, c_4151])).
% 5.81/2.15  tff(c_4156, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_2949])).
% 5.81/2.15  tff(c_4166, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4156, c_52])).
% 5.81/2.15  tff(c_4159, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4156, c_2927])).
% 5.81/2.15  tff(c_4162, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4156, c_2922])).
% 5.81/2.15  tff(c_36, plain, (![A_27, B_28, D_30]: (r2_relset_1(A_27, B_28, D_30, D_30) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.81/2.15  tff(c_4307, plain, (![D_513]: (r2_relset_1('#skF_3', '#skF_4', D_513, D_513) | ~m1_subset_1(D_513, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_4162, c_36])).
% 5.81/2.15  tff(c_4309, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_4159, c_4307])).
% 5.81/2.15  tff(c_4316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4166, c_4309])).
% 5.81/2.15  tff(c_4347, plain, (![A_516]: (~r2_hidden(A_516, '#skF_6'))), inference(splitRight, [status(thm)], [c_221])).
% 5.81/2.15  tff(c_4352, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_4347])).
% 5.81/2.15  tff(c_4318, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_221])).
% 5.81/2.15  tff(c_222, plain, (![A_68]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_68, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_213])).
% 5.81/2.15  tff(c_4319, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_222])).
% 5.81/2.15  tff(c_4344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4318, c_4319])).
% 5.81/2.15  tff(c_4357, plain, (![A_520]: (~r2_hidden(A_520, '#skF_5'))), inference(splitRight, [status(thm)], [c_222])).
% 5.81/2.15  tff(c_4381, plain, (![B_522]: (r1_tarski('#skF_5', B_522))), inference(resolution, [status(thm)], [c_6, c_4357])).
% 5.81/2.15  tff(c_4398, plain, (![B_523]: (B_523='#skF_5' | ~r1_tarski(B_523, '#skF_5'))), inference(resolution, [status(thm)], [c_4381, c_10])).
% 5.81/2.15  tff(c_4413, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_4352, c_4398])).
% 5.81/2.15  tff(c_4423, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4413, c_52])).
% 5.81/2.15  tff(c_4589, plain, (![A_532, B_533, D_534]: (r2_relset_1(A_532, B_533, D_534, D_534) | ~m1_subset_1(D_534, k1_zfmisc_1(k2_zfmisc_1(A_532, B_533))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.81/2.15  tff(c_4598, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_4589])).
% 5.81/2.15  tff(c_4603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4423, c_4598])).
% 5.81/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.15  
% 5.81/2.15  Inference rules
% 5.81/2.15  ----------------------
% 5.81/2.15  #Ref     : 3
% 5.81/2.15  #Sup     : 930
% 5.81/2.15  #Fact    : 0
% 5.81/2.15  #Define  : 0
% 5.81/2.15  #Split   : 33
% 5.81/2.15  #Chain   : 0
% 5.81/2.15  #Close   : 0
% 5.81/2.15  
% 5.81/2.15  Ordering : KBO
% 5.81/2.15  
% 5.81/2.15  Simplification rules
% 5.81/2.15  ----------------------
% 5.81/2.15  #Subsume      : 219
% 5.81/2.15  #Demod        : 970
% 5.81/2.15  #Tautology    : 471
% 5.81/2.15  #SimpNegUnit  : 20
% 5.81/2.15  #BackRed      : 306
% 5.81/2.15  
% 5.81/2.15  #Partial instantiations: 0
% 5.81/2.15  #Strategies tried      : 1
% 5.81/2.15  
% 5.81/2.15  Timing (in seconds)
% 5.81/2.15  ----------------------
% 5.81/2.15  Preprocessing        : 0.35
% 5.81/2.15  Parsing              : 0.18
% 5.81/2.15  CNF conversion       : 0.02
% 5.81/2.15  Main loop            : 1.00
% 5.81/2.15  Inferencing          : 0.33
% 5.81/2.15  Reduction            : 0.34
% 5.81/2.15  Demodulation         : 0.23
% 5.81/2.15  BG Simplification    : 0.04
% 5.81/2.15  Subsumption          : 0.20
% 5.81/2.15  Abstraction          : 0.04
% 5.81/2.15  MUC search           : 0.00
% 5.81/2.15  Cooper               : 0.00
% 5.81/2.15  Total                : 1.41
% 5.81/2.15  Index Insertion      : 0.00
% 5.81/2.15  Index Deletion       : 0.00
% 5.81/2.15  Index Matching       : 0.00
% 5.81/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
