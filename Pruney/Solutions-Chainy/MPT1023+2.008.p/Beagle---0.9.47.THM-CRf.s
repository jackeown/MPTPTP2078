%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:17 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 508 expanded)
%              Number of leaves         :   36 ( 183 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 (1477 expanded)
%              Number of equality atoms :   63 ( 241 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_72,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_214,plain,(
    ! [C_83,B_84,A_85] :
      ( v1_xboole_0(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(B_84,A_85)))
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_231,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_214])).

tff(c_233,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_286,plain,(
    ! [A_94,B_95,D_96] :
      ( r2_relset_1(A_94,B_95,D_96,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_300,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_286])).

tff(c_94,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_107,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_94])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_412,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_433,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_412])).

tff(c_695,plain,(
    ! [B_133,A_134,C_135] :
      ( k1_xboole_0 = B_133
      | k1_relset_1(A_134,B_133,C_135) = A_134
      | ~ v1_funct_2(C_135,A_134,B_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_715,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_695])).

tff(c_724,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_433,c_715])).

tff(c_731,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_106,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_94])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_432,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_412])).

tff(c_712,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_695])).

tff(c_721,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_432,c_712])).

tff(c_725,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_721])).

tff(c_880,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_2'(A_143,B_144),k1_relat_1(A_143))
      | B_144 = A_143
      | k1_relat_1(B_144) != k1_relat_1(A_143)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_893,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_2'('#skF_5',B_144),'#skF_3')
      | B_144 = '#skF_5'
      | k1_relat_1(B_144) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_880])).

tff(c_903,plain,(
    ! [B_145] :
      ( r2_hidden('#skF_2'('#skF_5',B_145),'#skF_3')
      | B_145 = '#skF_5'
      | k1_relat_1(B_145) != '#skF_3'
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_64,c_725,c_893])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1544,plain,(
    ! [B_214] :
      ( m1_subset_1('#skF_2'('#skF_5',B_214),'#skF_3')
      | B_214 = '#skF_5'
      | k1_relat_1(B_214) != '#skF_3'
      | ~ v1_funct_1(B_214)
      | ~ v1_relat_1(B_214) ) ),
    inference(resolution,[status(thm)],[c_903,c_16])).

tff(c_52,plain,(
    ! [E_42] :
      ( k1_funct_1('#skF_5',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ m1_subset_1(E_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2038,plain,(
    ! [B_246] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_246)) = k1_funct_1('#skF_6','#skF_2'('#skF_5',B_246))
      | B_246 = '#skF_5'
      | k1_relat_1(B_246) != '#skF_3'
      | ~ v1_funct_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(resolution,[status(thm)],[c_1544,c_52])).

tff(c_24,plain,(
    ! [B_19,A_15] :
      ( k1_funct_1(B_19,'#skF_2'(A_15,B_19)) != k1_funct_1(A_15,'#skF_2'(A_15,B_19))
      | B_19 = A_15
      | k1_relat_1(B_19) != k1_relat_1(A_15)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2044,plain,(
    ! [B_246] :
      ( k1_funct_1(B_246,'#skF_2'('#skF_5',B_246)) != k1_funct_1('#skF_6','#skF_2'('#skF_5',B_246))
      | B_246 = '#skF_5'
      | k1_relat_1(B_246) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_246)
      | ~ v1_relat_1(B_246)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | B_246 = '#skF_5'
      | k1_relat_1(B_246) != '#skF_3'
      | ~ v1_funct_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2038,c_24])).

tff(c_2050,plain,(
    ! [B_246] :
      ( k1_funct_1(B_246,'#skF_2'('#skF_5',B_246)) != k1_funct_1('#skF_6','#skF_2'('#skF_5',B_246))
      | B_246 = '#skF_5'
      | k1_relat_1(B_246) != '#skF_3'
      | ~ v1_funct_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_64,c_725,c_2044])).

tff(c_2934,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_6') != '#skF_3'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2050])).

tff(c_2936,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_58,c_731,c_2934])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2962,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2936,c_50])).

tff(c_2973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_2962])).

tff(c_2974,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3000,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_8])).

tff(c_3002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_3000])).

tff(c_3003,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_721])).

tff(c_3029,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_8])).

tff(c_3031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_3029])).

tff(c_3033,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_232,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_214])).

tff(c_3059,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3033,c_232])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_159,plain,(
    ! [C_70,B_71,A_72] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_183,plain,(
    ! [B_74,A_75,A_76] :
      ( ~ v1_xboole_0(B_74)
      | ~ r2_hidden(A_75,A_76)
      | ~ r1_tarski(A_76,B_74) ) ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_187,plain,(
    ! [B_77,A_78,B_79] :
      ( ~ v1_xboole_0(B_77)
      | ~ r1_tarski(A_78,B_77)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_196,plain,(
    ! [B_7,B_79] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_79) ) ),
    inference(resolution,[status(thm)],[c_14,c_187])).

tff(c_197,plain,(
    ! [B_80,B_81] :
      ( ~ v1_xboole_0(B_80)
      | r1_tarski(B_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_14,c_187])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3065,plain,(
    ! [B_292,B_291] :
      ( B_292 = B_291
      | ~ r1_tarski(B_291,B_292)
      | ~ v1_xboole_0(B_292) ) ),
    inference(resolution,[status(thm)],[c_197,c_10])).

tff(c_3083,plain,(
    ! [B_294,B_293] :
      ( B_294 = B_293
      | ~ v1_xboole_0(B_293)
      | ~ v1_xboole_0(B_294) ) ),
    inference(resolution,[status(thm)],[c_196,c_3065])).

tff(c_3096,plain,(
    ! [B_295] :
      ( B_295 = '#skF_6'
      | ~ v1_xboole_0(B_295) ) ),
    inference(resolution,[status(thm)],[c_3059,c_3083])).

tff(c_3111,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3033,c_3096])).

tff(c_3032,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_3112,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3032,c_3096])).

tff(c_3131,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3111,c_3112])).

tff(c_3043,plain,(
    ! [A_288,B_289,D_290] :
      ( r2_relset_1(A_288,B_289,D_290,D_290)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3056,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_3043])).

tff(c_3132,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_3131,c_3056])).

tff(c_3122,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3111,c_50])).

tff(c_3198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3132,c_3131,c_3122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.94  
% 5.02/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.94  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.02/1.94  
% 5.02/1.94  %Foreground sorts:
% 5.02/1.94  
% 5.02/1.94  
% 5.02/1.94  %Background operators:
% 5.02/1.94  
% 5.02/1.94  
% 5.02/1.94  %Foreground operators:
% 5.02/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.02/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/1.94  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.02/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.02/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/1.94  tff('#skF_5', type, '#skF_5': $i).
% 5.02/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.02/1.94  tff('#skF_6', type, '#skF_6': $i).
% 5.02/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.02/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.02/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.02/1.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.02/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.02/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.02/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.02/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.02/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.02/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.02/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.02/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.02/1.94  
% 5.02/1.96  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 5.02/1.96  tff(f_83, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.02/1.96  tff(f_95, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.02/1.96  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.02/1.96  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.02/1.96  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.02/1.96  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.02/1.96  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.02/1.96  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.02/1.96  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.02/1.96  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.02/1.96  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.02/1.96  tff(f_54, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.02/1.96  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.02/1.96  tff(c_214, plain, (![C_83, B_84, A_85]: (v1_xboole_0(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(B_84, A_85))) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.96  tff(c_231, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_214])).
% 5.02/1.96  tff(c_233, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_231])).
% 5.02/1.96  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.02/1.96  tff(c_286, plain, (![A_94, B_95, D_96]: (r2_relset_1(A_94, B_95, D_96, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.02/1.96  tff(c_300, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_286])).
% 5.02/1.96  tff(c_94, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.02/1.96  tff(c_107, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_94])).
% 5.02/1.96  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.02/1.96  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.02/1.96  tff(c_412, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.02/1.96  tff(c_433, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_412])).
% 5.02/1.96  tff(c_695, plain, (![B_133, A_134, C_135]: (k1_xboole_0=B_133 | k1_relset_1(A_134, B_133, C_135)=A_134 | ~v1_funct_2(C_135, A_134, B_133) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.02/1.96  tff(c_715, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_695])).
% 5.02/1.96  tff(c_724, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_433, c_715])).
% 5.02/1.96  tff(c_731, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_724])).
% 5.02/1.96  tff(c_106, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_94])).
% 5.02/1.96  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.02/1.96  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.02/1.96  tff(c_432, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_412])).
% 5.02/1.96  tff(c_712, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_695])).
% 5.02/1.96  tff(c_721, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_432, c_712])).
% 5.02/1.96  tff(c_725, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_721])).
% 5.02/1.96  tff(c_880, plain, (![A_143, B_144]: (r2_hidden('#skF_2'(A_143, B_144), k1_relat_1(A_143)) | B_144=A_143 | k1_relat_1(B_144)!=k1_relat_1(A_143) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.02/1.96  tff(c_893, plain, (![B_144]: (r2_hidden('#skF_2'('#skF_5', B_144), '#skF_3') | B_144='#skF_5' | k1_relat_1(B_144)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_725, c_880])).
% 5.02/1.96  tff(c_903, plain, (![B_145]: (r2_hidden('#skF_2'('#skF_5', B_145), '#skF_3') | B_145='#skF_5' | k1_relat_1(B_145)!='#skF_3' | ~v1_funct_1(B_145) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_64, c_725, c_893])).
% 5.02/1.96  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/1.96  tff(c_1544, plain, (![B_214]: (m1_subset_1('#skF_2'('#skF_5', B_214), '#skF_3') | B_214='#skF_5' | k1_relat_1(B_214)!='#skF_3' | ~v1_funct_1(B_214) | ~v1_relat_1(B_214))), inference(resolution, [status(thm)], [c_903, c_16])).
% 5.02/1.96  tff(c_52, plain, (![E_42]: (k1_funct_1('#skF_5', E_42)=k1_funct_1('#skF_6', E_42) | ~m1_subset_1(E_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.02/1.96  tff(c_2038, plain, (![B_246]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_246))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_246)) | B_246='#skF_5' | k1_relat_1(B_246)!='#skF_3' | ~v1_funct_1(B_246) | ~v1_relat_1(B_246))), inference(resolution, [status(thm)], [c_1544, c_52])).
% 5.02/1.96  tff(c_24, plain, (![B_19, A_15]: (k1_funct_1(B_19, '#skF_2'(A_15, B_19))!=k1_funct_1(A_15, '#skF_2'(A_15, B_19)) | B_19=A_15 | k1_relat_1(B_19)!=k1_relat_1(A_15) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.02/1.96  tff(c_2044, plain, (![B_246]: (k1_funct_1(B_246, '#skF_2'('#skF_5', B_246))!=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_246)) | B_246='#skF_5' | k1_relat_1(B_246)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_246) | ~v1_relat_1(B_246) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | B_246='#skF_5' | k1_relat_1(B_246)!='#skF_3' | ~v1_funct_1(B_246) | ~v1_relat_1(B_246))), inference(superposition, [status(thm), theory('equality')], [c_2038, c_24])).
% 5.02/1.96  tff(c_2050, plain, (![B_246]: (k1_funct_1(B_246, '#skF_2'('#skF_5', B_246))!=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_246)) | B_246='#skF_5' | k1_relat_1(B_246)!='#skF_3' | ~v1_funct_1(B_246) | ~v1_relat_1(B_246))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_64, c_725, c_2044])).
% 5.02/1.96  tff(c_2934, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_6')!='#skF_3' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(reflexivity, [status(thm), theory('equality')], [c_2050])).
% 5.02/1.96  tff(c_2936, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_58, c_731, c_2934])).
% 5.02/1.96  tff(c_50, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.02/1.96  tff(c_2962, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2936, c_50])).
% 5.02/1.96  tff(c_2973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_2962])).
% 5.02/1.96  tff(c_2974, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_724])).
% 5.02/1.96  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.02/1.96  tff(c_3000, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2974, c_8])).
% 5.02/1.96  tff(c_3002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_3000])).
% 5.02/1.96  tff(c_3003, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_721])).
% 5.02/1.96  tff(c_3029, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_8])).
% 5.02/1.96  tff(c_3031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_3029])).
% 5.02/1.96  tff(c_3033, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_231])).
% 5.02/1.96  tff(c_232, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_214])).
% 5.02/1.96  tff(c_3059, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3033, c_232])).
% 5.02/1.96  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.02/1.96  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.02/1.96  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.02/1.96  tff(c_159, plain, (![C_70, B_71, A_72]: (~v1_xboole_0(C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.02/1.96  tff(c_183, plain, (![B_74, A_75, A_76]: (~v1_xboole_0(B_74) | ~r2_hidden(A_75, A_76) | ~r1_tarski(A_76, B_74))), inference(resolution, [status(thm)], [c_20, c_159])).
% 5.02/1.96  tff(c_187, plain, (![B_77, A_78, B_79]: (~v1_xboole_0(B_77) | ~r1_tarski(A_78, B_77) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_6, c_183])).
% 5.02/1.96  tff(c_196, plain, (![B_7, B_79]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_79))), inference(resolution, [status(thm)], [c_14, c_187])).
% 5.02/1.96  tff(c_197, plain, (![B_80, B_81]: (~v1_xboole_0(B_80) | r1_tarski(B_80, B_81))), inference(resolution, [status(thm)], [c_14, c_187])).
% 5.02/1.96  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.02/1.96  tff(c_3065, plain, (![B_292, B_291]: (B_292=B_291 | ~r1_tarski(B_291, B_292) | ~v1_xboole_0(B_292))), inference(resolution, [status(thm)], [c_197, c_10])).
% 5.02/1.96  tff(c_3083, plain, (![B_294, B_293]: (B_294=B_293 | ~v1_xboole_0(B_293) | ~v1_xboole_0(B_294))), inference(resolution, [status(thm)], [c_196, c_3065])).
% 5.02/1.96  tff(c_3096, plain, (![B_295]: (B_295='#skF_6' | ~v1_xboole_0(B_295))), inference(resolution, [status(thm)], [c_3059, c_3083])).
% 5.02/1.96  tff(c_3111, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_3033, c_3096])).
% 5.02/1.96  tff(c_3032, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_231])).
% 5.02/1.96  tff(c_3112, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_3032, c_3096])).
% 5.02/1.96  tff(c_3131, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3111, c_3112])).
% 5.02/1.96  tff(c_3043, plain, (![A_288, B_289, D_290]: (r2_relset_1(A_288, B_289, D_290, D_290) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.02/1.96  tff(c_3056, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_3043])).
% 5.02/1.96  tff(c_3132, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_3131, c_3056])).
% 5.02/1.96  tff(c_3122, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3111, c_50])).
% 5.02/1.96  tff(c_3198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3132, c_3131, c_3122])).
% 5.02/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.96  
% 5.02/1.96  Inference rules
% 5.02/1.96  ----------------------
% 5.02/1.96  #Ref     : 2
% 5.02/1.96  #Sup     : 677
% 5.02/1.96  #Fact    : 0
% 5.02/1.96  #Define  : 0
% 5.02/1.96  #Split   : 11
% 5.02/1.96  #Chain   : 0
% 5.02/1.96  #Close   : 0
% 5.02/1.96  
% 5.02/1.96  Ordering : KBO
% 5.02/1.96  
% 5.02/1.96  Simplification rules
% 5.02/1.96  ----------------------
% 5.02/1.96  #Subsume      : 152
% 5.02/1.96  #Demod        : 481
% 5.02/1.96  #Tautology    : 228
% 5.02/1.96  #SimpNegUnit  : 8
% 5.02/1.96  #BackRed      : 98
% 5.02/1.96  
% 5.02/1.96  #Partial instantiations: 0
% 5.02/1.96  #Strategies tried      : 1
% 5.02/1.96  
% 5.02/1.96  Timing (in seconds)
% 5.02/1.96  ----------------------
% 5.02/1.96  Preprocessing        : 0.36
% 5.02/1.96  Parsing              : 0.19
% 5.02/1.96  CNF conversion       : 0.02
% 5.02/1.96  Main loop            : 0.81
% 5.02/1.96  Inferencing          : 0.27
% 5.02/1.96  Reduction            : 0.25
% 5.02/1.96  Demodulation         : 0.17
% 5.02/1.96  BG Simplification    : 0.03
% 5.02/1.96  Subsumption          : 0.19
% 5.02/1.96  Abstraction          : 0.04
% 5.02/1.96  MUC search           : 0.00
% 5.02/1.97  Cooper               : 0.00
% 5.02/1.97  Total                : 1.20
% 5.02/1.97  Index Insertion      : 0.00
% 5.02/1.97  Index Deletion       : 0.00
% 5.02/1.97  Index Matching       : 0.00
% 5.02/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
