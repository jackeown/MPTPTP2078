%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:03 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 163 expanded)
%              Number of leaves         :   39 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  152 ( 395 expanded)
%              Number of equality atoms :   35 ( 101 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_139,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_148,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_139])).

tff(c_56,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_24,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_102,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_102])).

tff(c_112,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_108])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_226,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_235,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_226])).

tff(c_422,plain,(
    ! [B_132,A_133,C_134] :
      ( k1_xboole_0 = B_132
      | k1_relset_1(A_133,B_132,C_134) = A_133
      | ~ v1_funct_2(C_134,A_133,B_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_429,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_422])).

tff(c_433,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_235,c_429])).

tff(c_434,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_433])).

tff(c_32,plain,(
    ! [C_26,B_25,A_24] :
      ( m1_subset_1(k1_funct_1(C_26,B_25),A_24)
      | ~ r2_hidden(B_25,k1_relat_1(C_26))
      | ~ v1_funct_1(C_26)
      | ~ v5_relat_1(C_26,A_24)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_447,plain,(
    ! [B_25,A_24] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_25),A_24)
      | ~ r2_hidden(B_25,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_24)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_32])).

tff(c_630,plain,(
    ! [B_144,A_145] :
      ( m1_subset_1(k1_funct_1('#skF_5',B_144),A_145)
      | ~ r2_hidden(B_144,'#skF_2')
      | ~ v5_relat_1('#skF_5',A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_62,c_447])).

tff(c_129,plain,(
    ! [A_59,B_60] :
      ( r2_hidden(A_59,B_60)
      | v1_xboole_0(B_60)
      | ~ m1_subset_1(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_136,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_52])).

tff(c_138,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_665,plain,
    ( ~ r2_hidden('#skF_4','#skF_2')
    | ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_630,c_138])).

tff(c_685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_56,c_665])).

tff(c_686,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [B_39,A_40] :
      ( ~ r2_hidden(B_39,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_66])).

tff(c_80,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_88,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_80])).

tff(c_761,plain,(
    ! [A_172,B_173,C_174] :
      ( k1_relset_1(A_172,B_173,C_174) = k1_relat_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_770,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_761])).

tff(c_1022,plain,(
    ! [B_225,A_226,C_227] :
      ( k1_xboole_0 = B_225
      | k1_relset_1(A_226,B_225,C_227) = A_226
      | ~ v1_funct_2(C_227,A_226,B_225)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1029,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1022])).

tff(c_1033,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_770,c_1029])).

tff(c_1034,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1033])).

tff(c_746,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(k1_relat_1(A_170),k1_relat_1(B_171))
      | ~ r1_tarski(A_170,B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_19,B_20)),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_89,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_19,B_20] :
      ( k1_relat_1(k2_zfmisc_1(A_19,B_20)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(resolution,[status(thm)],[c_26,c_89])).

tff(c_750,plain,(
    ! [A_170,B_20] :
      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(A_170),B_20)) = k1_relat_1(A_170)
      | ~ r1_tarski(A_170,k2_zfmisc_1(k1_relat_1(A_170),B_20))
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(A_170),B_20))
      | ~ v1_relat_1(A_170) ) ),
    inference(resolution,[status(thm)],[c_746,c_97])).

tff(c_758,plain,(
    ! [A_170,B_20] :
      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(A_170),B_20)) = k1_relat_1(A_170)
      | ~ r1_tarski(A_170,k2_zfmisc_1(k1_relat_1(A_170),B_20))
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_750])).

tff(c_1045,plain,(
    ! [B_20] :
      ( k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_20)) = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_20))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_758])).

tff(c_1145,plain,(
    ! [B_233] :
      ( k1_relat_1(k2_zfmisc_1('#skF_2',B_233)) = '#skF_2'
      | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_2',B_233)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1034,c_1034,c_1045])).

tff(c_1149,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_88,c_1145])).

tff(c_22,plain,(
    ! [A_16] :
      ( v1_xboole_0(k1_relat_1(A_16))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1190,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_22])).

tff(c_1217,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1190])).

tff(c_1240,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1217])).

tff(c_1244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_1240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.55  
% 3.41/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.55  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.41/1.55  
% 3.41/1.55  %Foreground sorts:
% 3.41/1.55  
% 3.41/1.55  
% 3.41/1.55  %Background operators:
% 3.41/1.55  
% 3.41/1.55  
% 3.41/1.55  %Foreground operators:
% 3.41/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.41/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.41/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.41/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.41/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.41/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.41/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.41/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.41/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.41/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.41/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.41/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.41/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.41/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.55  
% 3.41/1.57  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.41/1.57  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.41/1.57  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.41/1.57  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.41/1.57  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.41/1.57  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.41/1.57  tff(f_87, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 3.41/1.57  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.41/1.57  tff(f_41, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.41/1.57  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.41/1.57  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.41/1.57  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.41/1.57  tff(f_66, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 3.41/1.57  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.41/1.57  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.41/1.57  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.41/1.57  tff(c_139, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.41/1.57  tff(c_148, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_139])).
% 3.41/1.57  tff(c_56, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.41/1.57  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.41/1.57  tff(c_102, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.41/1.57  tff(c_108, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_102])).
% 3.41/1.57  tff(c_112, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_108])).
% 3.41/1.57  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.41/1.57  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.41/1.57  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.41/1.57  tff(c_226, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.41/1.57  tff(c_235, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_226])).
% 3.41/1.57  tff(c_422, plain, (![B_132, A_133, C_134]: (k1_xboole_0=B_132 | k1_relset_1(A_133, B_132, C_134)=A_133 | ~v1_funct_2(C_134, A_133, B_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.41/1.57  tff(c_429, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_422])).
% 3.41/1.57  tff(c_433, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_235, c_429])).
% 3.41/1.57  tff(c_434, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_433])).
% 3.41/1.57  tff(c_32, plain, (![C_26, B_25, A_24]: (m1_subset_1(k1_funct_1(C_26, B_25), A_24) | ~r2_hidden(B_25, k1_relat_1(C_26)) | ~v1_funct_1(C_26) | ~v5_relat_1(C_26, A_24) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.41/1.57  tff(c_447, plain, (![B_25, A_24]: (m1_subset_1(k1_funct_1('#skF_5', B_25), A_24) | ~r2_hidden(B_25, '#skF_2') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_24) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_434, c_32])).
% 3.41/1.57  tff(c_630, plain, (![B_144, A_145]: (m1_subset_1(k1_funct_1('#skF_5', B_144), A_145) | ~r2_hidden(B_144, '#skF_2') | ~v5_relat_1('#skF_5', A_145))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_62, c_447])).
% 3.41/1.57  tff(c_129, plain, (![A_59, B_60]: (r2_hidden(A_59, B_60) | v1_xboole_0(B_60) | ~m1_subset_1(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.41/1.57  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.41/1.57  tff(c_136, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_129, c_52])).
% 3.41/1.57  tff(c_138, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_136])).
% 3.41/1.57  tff(c_665, plain, (~r2_hidden('#skF_4', '#skF_2') | ~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_630, c_138])).
% 3.41/1.57  tff(c_685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_56, c_665])).
% 3.41/1.57  tff(c_686, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_136])).
% 3.41/1.57  tff(c_12, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.41/1.57  tff(c_66, plain, (![B_39, A_40]: (~r2_hidden(B_39, A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.57  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_66])).
% 3.41/1.57  tff(c_80, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.41/1.57  tff(c_88, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_80])).
% 3.41/1.57  tff(c_761, plain, (![A_172, B_173, C_174]: (k1_relset_1(A_172, B_173, C_174)=k1_relat_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.41/1.57  tff(c_770, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_761])).
% 3.41/1.57  tff(c_1022, plain, (![B_225, A_226, C_227]: (k1_xboole_0=B_225 | k1_relset_1(A_226, B_225, C_227)=A_226 | ~v1_funct_2(C_227, A_226, B_225) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.41/1.57  tff(c_1029, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_1022])).
% 3.41/1.57  tff(c_1033, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_770, c_1029])).
% 3.41/1.57  tff(c_1034, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_1033])).
% 3.41/1.57  tff(c_746, plain, (![A_170, B_171]: (r1_tarski(k1_relat_1(A_170), k1_relat_1(B_171)) | ~r1_tarski(A_170, B_171) | ~v1_relat_1(B_171) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.57  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_19, B_20)), A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.41/1.57  tff(c_89, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.41/1.57  tff(c_97, plain, (![A_19, B_20]: (k1_relat_1(k2_zfmisc_1(A_19, B_20))=A_19 | ~r1_tarski(A_19, k1_relat_1(k2_zfmisc_1(A_19, B_20))))), inference(resolution, [status(thm)], [c_26, c_89])).
% 3.41/1.57  tff(c_750, plain, (![A_170, B_20]: (k1_relat_1(k2_zfmisc_1(k1_relat_1(A_170), B_20))=k1_relat_1(A_170) | ~r1_tarski(A_170, k2_zfmisc_1(k1_relat_1(A_170), B_20)) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(A_170), B_20)) | ~v1_relat_1(A_170))), inference(resolution, [status(thm)], [c_746, c_97])).
% 3.41/1.57  tff(c_758, plain, (![A_170, B_20]: (k1_relat_1(k2_zfmisc_1(k1_relat_1(A_170), B_20))=k1_relat_1(A_170) | ~r1_tarski(A_170, k2_zfmisc_1(k1_relat_1(A_170), B_20)) | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_750])).
% 3.41/1.57  tff(c_1045, plain, (![B_20]: (k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_20))=k1_relat_1('#skF_5') | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_20)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1034, c_758])).
% 3.41/1.57  tff(c_1145, plain, (![B_233]: (k1_relat_1(k2_zfmisc_1('#skF_2', B_233))='#skF_2' | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', B_233)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1034, c_1034, c_1045])).
% 3.41/1.57  tff(c_1149, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_88, c_1145])).
% 3.41/1.57  tff(c_22, plain, (![A_16]: (v1_xboole_0(k1_relat_1(A_16)) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.41/1.57  tff(c_1190, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1149, c_22])).
% 3.41/1.57  tff(c_1217, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1190])).
% 3.41/1.57  tff(c_1240, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1217])).
% 3.41/1.57  tff(c_1244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_686, c_1240])).
% 3.41/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.57  
% 3.41/1.57  Inference rules
% 3.41/1.57  ----------------------
% 3.41/1.57  #Ref     : 0
% 3.41/1.57  #Sup     : 234
% 3.41/1.57  #Fact    : 0
% 3.41/1.57  #Define  : 0
% 3.41/1.57  #Split   : 5
% 3.41/1.57  #Chain   : 0
% 3.41/1.57  #Close   : 0
% 3.41/1.57  
% 3.41/1.57  Ordering : KBO
% 3.41/1.57  
% 3.41/1.57  Simplification rules
% 3.41/1.57  ----------------------
% 3.41/1.57  #Subsume      : 30
% 3.41/1.57  #Demod        : 143
% 3.41/1.57  #Tautology    : 58
% 3.41/1.57  #SimpNegUnit  : 14
% 3.41/1.57  #BackRed      : 2
% 3.41/1.57  
% 3.41/1.57  #Partial instantiations: 0
% 3.41/1.57  #Strategies tried      : 1
% 3.41/1.57  
% 3.41/1.57  Timing (in seconds)
% 3.41/1.57  ----------------------
% 3.41/1.57  Preprocessing        : 0.34
% 3.41/1.57  Parsing              : 0.18
% 3.41/1.57  CNF conversion       : 0.02
% 3.41/1.57  Main loop            : 0.45
% 3.41/1.57  Inferencing          : 0.17
% 3.41/1.57  Reduction            : 0.14
% 3.41/1.57  Demodulation         : 0.10
% 3.41/1.57  BG Simplification    : 0.02
% 3.41/1.57  Subsumption          : 0.09
% 3.41/1.57  Abstraction          : 0.02
% 3.41/1.57  MUC search           : 0.00
% 3.41/1.57  Cooper               : 0.00
% 3.41/1.57  Total                : 0.83
% 3.41/1.57  Index Insertion      : 0.00
% 3.41/1.57  Index Deletion       : 0.00
% 3.41/1.57  Index Matching       : 0.00
% 3.41/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
