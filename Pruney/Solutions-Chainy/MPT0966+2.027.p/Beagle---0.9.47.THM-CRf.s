%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:12 EST 2020

% Result     : Theorem 8.57s
% Output     : CNFRefutation 8.78s
% Verified   : 
% Statistics : Number of formulae       :  291 (2157 expanded)
%              Number of leaves         :   41 ( 701 expanded)
%              Depth                    :   13
%              Number of atoms          :  507 (5794 expanded)
%              Number of equality atoms :  179 (1872 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_83,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_20,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_9817,plain,(
    ! [A_793,B_794,C_795] :
      ( k1_relset_1(A_793,B_794,C_795) = k1_relat_1(C_795)
      | ~ m1_subset_1(C_795,k1_zfmisc_1(k2_zfmisc_1(A_793,B_794))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9832,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_9817])).

tff(c_10269,plain,(
    ! [B_846,A_847,C_848] :
      ( k1_xboole_0 = B_846
      | k1_relset_1(A_847,B_846,C_848) = A_847
      | ~ v1_funct_2(C_848,A_847,B_846)
      | ~ m1_subset_1(C_848,k1_zfmisc_1(k2_zfmisc_1(A_847,B_846))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_10279,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_10269])).

tff(c_10290,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9832,c_10279])).

tff(c_10291,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_10290])).

tff(c_38,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9558,plain,(
    ! [B_754,A_755] :
      ( v1_relat_1(B_754)
      | ~ m1_subset_1(B_754,k1_zfmisc_1(A_755))
      | ~ v1_relat_1(A_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9564,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_9558])).

tff(c_9568,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_9564])).

tff(c_9934,plain,(
    ! [A_806,B_807,C_808] :
      ( k2_relset_1(A_806,B_807,C_808) = k2_relat_1(C_808)
      | ~ m1_subset_1(C_808,k1_zfmisc_1(k2_zfmisc_1(A_806,B_807))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9949,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_9934])).

tff(c_66,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_10022,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9949,c_66])).

tff(c_10148,plain,(
    ! [C_830,A_831,B_832] :
      ( m1_subset_1(C_830,k1_zfmisc_1(k2_zfmisc_1(A_831,B_832)))
      | ~ r1_tarski(k2_relat_1(C_830),B_832)
      | ~ r1_tarski(k1_relat_1(C_830),A_831)
      | ~ v1_relat_1(C_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_24] :
      ( v1_xboole_0(k1_relat_1(A_24))
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_112,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_3'(A_48),A_48)
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(A_49)
      | k1_xboole_0 = A_49 ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_132,plain,(
    ! [A_51] :
      ( k1_relat_1(A_51) = k1_xboole_0
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_36,c_117])).

tff(c_140,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,(
    ! [A_37] :
      ( v1_funct_2(k1_xboole_0,A_37,k1_xboole_0)
      | k1_xboole_0 = A_37
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_37,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_77,plain,(
    ! [A_37] :
      ( v1_funct_2(k1_xboole_0,A_37,k1_xboole_0)
      | k1_xboole_0 = A_37
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_50])).

tff(c_6300,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_6303,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_6300])).

tff(c_6307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6303])).

tff(c_6309,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_32,plain,(
    ! [C_20,B_19,A_18] :
      ( ~ v1_xboole_0(C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6311,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6309,c_32])).

tff(c_6326,plain,(
    ! [A_459] : ~ r2_hidden(A_459,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6311])).

tff(c_6339,plain,(
    ! [B_6] : r1_tarski(k1_xboole_0,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_6326])).

tff(c_199,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_205,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_199])).

tff(c_209,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_205])).

tff(c_239,plain,(
    ! [A_67] :
      ( k1_relat_1(A_67) = k1_xboole_0
      | k2_relat_1(A_67) != k1_xboole_0
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_249,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_209,c_239])).

tff(c_253,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_722,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_737,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_722])).

tff(c_1030,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_xboole_0 = B_172
      | k1_relset_1(A_173,B_172,C_174) = A_173
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1040,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1030])).

tff(c_1051,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_737,c_1040])).

tff(c_1052,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1051])).

tff(c_544,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_559,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_544])).

tff(c_632,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_66])).

tff(c_766,plain,(
    ! [C_134,A_135,B_136] :
      ( m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ r1_tarski(k2_relat_1(C_134),B_136)
      | ~ r1_tarski(k1_relat_1(C_134),A_135)
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2496,plain,(
    ! [C_246,A_247,B_248] :
      ( r1_tarski(C_246,k2_zfmisc_1(A_247,B_248))
      | ~ r1_tarski(k2_relat_1(C_246),B_248)
      | ~ r1_tarski(k1_relat_1(C_246),A_247)
      | ~ v1_relat_1(C_246) ) ),
    inference(resolution,[status(thm)],[c_766,c_28])).

tff(c_2504,plain,(
    ! [A_247] :
      ( r1_tarski('#skF_7',k2_zfmisc_1(A_247,'#skF_6'))
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_247)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_632,c_2496])).

tff(c_2526,plain,(
    ! [A_249] :
      ( r1_tarski('#skF_7',k2_zfmisc_1(A_249,'#skF_6'))
      | ~ r1_tarski('#skF_4',A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_1052,c_2504])).

tff(c_736,plain,(
    ! [A_127,B_128,A_16] :
      ( k1_relset_1(A_127,B_128,A_16) = k1_relat_1(A_16)
      | ~ r1_tarski(A_16,k2_zfmisc_1(A_127,B_128)) ) ),
    inference(resolution,[status(thm)],[c_30,c_722])).

tff(c_2534,plain,(
    ! [A_249] :
      ( k1_relset_1(A_249,'#skF_6','#skF_7') = k1_relat_1('#skF_7')
      | ~ r1_tarski('#skF_4',A_249) ) ),
    inference(resolution,[status(thm)],[c_2526,c_736])).

tff(c_2582,plain,(
    ! [A_251] :
      ( k1_relset_1(A_251,'#skF_6','#skF_7') = '#skF_4'
      | ~ r1_tarski('#skF_4',A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_2534])).

tff(c_2592,plain,(
    k1_relset_1('#skF_4','#skF_6','#skF_7') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_2582])).

tff(c_48,plain,(
    ! [C_36,A_34,B_35] :
      ( m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ r1_tarski(k2_relat_1(C_36),B_35)
      | ~ r1_tarski(k1_relat_1(C_36),A_34)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_887,plain,(
    ! [B_152,C_153,A_154] :
      ( k1_xboole_0 = B_152
      | v1_funct_2(C_153,A_154,B_152)
      | k1_relset_1(A_154,B_152,C_153) != A_154
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4449,plain,(
    ! [B_327,C_328,A_329] :
      ( k1_xboole_0 = B_327
      | v1_funct_2(C_328,A_329,B_327)
      | k1_relset_1(A_329,B_327,C_328) != A_329
      | ~ r1_tarski(k2_relat_1(C_328),B_327)
      | ~ r1_tarski(k1_relat_1(C_328),A_329)
      | ~ v1_relat_1(C_328) ) ),
    inference(resolution,[status(thm)],[c_48,c_887])).

tff(c_4457,plain,(
    ! [A_329] :
      ( k1_xboole_0 = '#skF_6'
      | v1_funct_2('#skF_7',A_329,'#skF_6')
      | k1_relset_1(A_329,'#skF_6','#skF_7') != A_329
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_329)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_632,c_4449])).

tff(c_4474,plain,(
    ! [A_329] :
      ( k1_xboole_0 = '#skF_6'
      | v1_funct_2('#skF_7',A_329,'#skF_6')
      | k1_relset_1(A_329,'#skF_6','#skF_7') != A_329
      | ~ r1_tarski('#skF_4',A_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_1052,c_4457])).

tff(c_5129,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4474])).

tff(c_429,plain,(
    ! [C_94,B_95,A_96] :
      ( r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_471,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_3'(A_104),B_105)
      | ~ r1_tarski(A_104,B_105)
      | k1_xboole_0 = A_104 ) ),
    inference(resolution,[status(thm)],[c_14,c_429])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4394,plain,(
    ! [A_322,B_323,B_324] :
      ( r2_hidden('#skF_3'(A_322),B_323)
      | ~ r1_tarski(B_324,B_323)
      | ~ r1_tarski(A_322,B_324)
      | k1_xboole_0 = A_322 ) ),
    inference(resolution,[status(thm)],[c_471,c_6])).

tff(c_4419,plain,(
    ! [A_325] :
      ( r2_hidden('#skF_3'(A_325),'#skF_6')
      | ~ r1_tarski(A_325,k2_relat_1('#skF_7'))
      | k1_xboole_0 = A_325 ) ),
    inference(resolution,[status(thm)],[c_632,c_4394])).

tff(c_4690,plain,(
    ! [A_336,B_337] :
      ( r2_hidden('#skF_3'(A_336),B_337)
      | ~ r1_tarski('#skF_6',B_337)
      | ~ r1_tarski(A_336,k2_relat_1('#skF_7'))
      | k1_xboole_0 = A_336 ) ),
    inference(resolution,[status(thm)],[c_4419,c_6])).

tff(c_490,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_493,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_490])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_493])).

tff(c_499,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_501,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_499,c_32])).

tff(c_510,plain,(
    ! [A_18] : ~ r2_hidden(A_18,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_501])).

tff(c_4710,plain,(
    ! [A_336] :
      ( ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r1_tarski(A_336,k2_relat_1('#skF_7'))
      | k1_xboole_0 = A_336 ) ),
    inference(resolution,[status(thm)],[c_4690,c_510])).

tff(c_4714,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4710])).

tff(c_5134,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5129,c_4714])).

tff(c_5210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5134])).

tff(c_5213,plain,(
    ! [A_357] :
      ( v1_funct_2('#skF_7',A_357,'#skF_6')
      | k1_relset_1(A_357,'#skF_6','#skF_7') != A_357
      | ~ r1_tarski('#skF_4',A_357) ) ),
    inference(splitRight,[status(thm)],[c_4474])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62])).

tff(c_150,plain,(
    ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_5221,plain,
    ( k1_relset_1('#skF_4','#skF_6','#skF_7') != '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5213,c_150])).

tff(c_5230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2592,c_5221])).

tff(c_5232,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4710])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_460,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_1'(A_102),B_103)
      | ~ r1_tarski(A_102,B_103)
      | v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_4,c_429])).

tff(c_4284,plain,(
    ! [A_312,B_313,B_314] :
      ( r2_hidden('#skF_1'(A_312),B_313)
      | ~ r1_tarski(B_314,B_313)
      | ~ r1_tarski(A_312,B_314)
      | v1_xboole_0(A_312) ) ),
    inference(resolution,[status(thm)],[c_460,c_6])).

tff(c_4309,plain,(
    ! [A_315] :
      ( r2_hidden('#skF_1'(A_315),'#skF_6')
      | ~ r1_tarski(A_315,k2_relat_1('#skF_7'))
      | v1_xboole_0(A_315) ) ),
    inference(resolution,[status(thm)],[c_632,c_4284])).

tff(c_378,plain,(
    ! [C_84,B_85,A_86] :
      ( ~ v1_xboole_0(C_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(C_84))
      | ~ r2_hidden(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_383,plain,(
    ! [B_17,A_86,A_16] :
      ( ~ v1_xboole_0(B_17)
      | ~ r2_hidden(A_86,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_30,c_378])).

tff(c_4321,plain,(
    ! [B_17,A_315] :
      ( ~ v1_xboole_0(B_17)
      | ~ r1_tarski('#skF_6',B_17)
      | ~ r1_tarski(A_315,k2_relat_1('#skF_7'))
      | v1_xboole_0(A_315) ) ),
    inference(resolution,[status(thm)],[c_4309,c_383])).

tff(c_4370,plain,(
    ! [B_17] :
      ( ~ v1_xboole_0(B_17)
      | ~ r1_tarski('#skF_6',B_17) ) ),
    inference(splitLeft,[status(thm)],[c_4321])).

tff(c_5237,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5232,c_4370])).

tff(c_5284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5237])).

tff(c_5286,plain,(
    ! [A_358] :
      ( ~ r1_tarski(A_358,k2_relat_1('#skF_7'))
      | v1_xboole_0(A_358) ) ),
    inference(splitRight,[status(thm)],[c_4321])).

tff(c_5312,plain,(
    v1_xboole_0(k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_20,c_5286])).

tff(c_116,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(A_48)
      | k1_xboole_0 = A_48 ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_5371,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5312,c_116])).

tff(c_5387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_5371])).

tff(c_5388,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_5787,plain,(
    ! [A_407,B_408,C_409] :
      ( k1_relset_1(A_407,B_408,C_409) = k1_relat_1(C_409)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(A_407,B_408))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5794,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_5787])).

tff(c_5803,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5388,c_5794])).

tff(c_6020,plain,(
    ! [B_443,A_444,C_445] :
      ( k1_xboole_0 = B_443
      | k1_relset_1(A_444,B_443,C_445) = A_444
      | ~ v1_funct_2(C_445,A_444,B_443)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_444,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6030,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_6020])).

tff(c_6041,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5803,c_6030])).

tff(c_6042,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6041])).

tff(c_5622,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_5625,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_5622])).

tff(c_5629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5625])).

tff(c_5631,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_5633,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5631,c_32])).

tff(c_5648,plain,(
    ! [A_395] : ~ r2_hidden(A_395,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5633])).

tff(c_5666,plain,(
    ! [B_6] : r1_tarski(k1_xboole_0,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_5648])).

tff(c_6068,plain,(
    ! [B_6] : r1_tarski('#skF_4',B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6042,c_5666])).

tff(c_26,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6084,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_4',B_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6042,c_6042,c_26])).

tff(c_178,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_186,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_178])).

tff(c_210,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_217,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_186,c_210])).

tff(c_5568,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_6237,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6084,c_5568])).

tff(c_6243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6068,c_6237])).

tff(c_6244,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_6344,plain,(
    ! [A_460,B_461,C_462] :
      ( k1_relset_1(A_460,B_461,C_462) = k1_relat_1(C_462)
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6478,plain,(
    ! [C_477] :
      ( k1_relset_1('#skF_4','#skF_5',C_477) = k1_relat_1(C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6244,c_6344])).

tff(c_6493,plain,(
    ! [A_478] :
      ( k1_relset_1('#skF_4','#skF_5',A_478) = k1_relat_1(A_478)
      | ~ r1_tarski(A_478,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_6478])).

tff(c_6497,plain,(
    k1_relset_1('#skF_4','#skF_5',k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6339,c_6493])).

tff(c_6507,plain,(
    k1_relset_1('#skF_4','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_6497])).

tff(c_83,plain,(
    ! [A_43] : k2_zfmisc_1(A_43,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_38])).

tff(c_5407,plain,(
    ! [A_362] :
      ( k2_relat_1(A_362) = k1_xboole_0
      | k1_relat_1(A_362) != k1_xboole_0
      | ~ v1_relat_1(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5413,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_5407])).

tff(c_5422,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_5413])).

tff(c_6895,plain,(
    ! [C_528,A_529,B_530] :
      ( m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530)))
      | ~ r1_tarski(k2_relat_1(C_528),B_530)
      | ~ r1_tarski(k1_relat_1(C_528),A_529)
      | ~ v1_relat_1(C_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6981,plain,(
    ! [C_537] :
      ( m1_subset_1(C_537,k1_zfmisc_1('#skF_7'))
      | ~ r1_tarski(k2_relat_1(C_537),'#skF_5')
      | ~ r1_tarski(k1_relat_1(C_537),'#skF_4')
      | ~ v1_relat_1(C_537) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6244,c_6895])).

tff(c_6993,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_7'))
    | ~ r1_tarski(k1_xboole_0,'#skF_5')
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5422,c_6981])).

tff(c_7003,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_6339,c_140,c_6339,c_6993])).

tff(c_7156,plain,(
    ! [B_545,C_546,A_547] :
      ( k1_xboole_0 = B_545
      | v1_funct_2(C_546,A_547,B_545)
      | k1_relset_1(A_547,B_545,C_546) != A_547
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(A_547,B_545))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_7162,plain,(
    ! [C_546] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2(C_546,'#skF_4','#skF_5')
      | k1_relset_1('#skF_4','#skF_5',C_546) != '#skF_4'
      | ~ m1_subset_1(C_546,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6244,c_7156])).

tff(c_7336,plain,(
    ! [C_550] :
      ( v1_funct_2(C_550,'#skF_4','#skF_5')
      | k1_relset_1('#skF_4','#skF_5',C_550) != '#skF_4'
      | ~ m1_subset_1(C_550,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7162])).

tff(c_7339,plain,
    ( v1_funct_2(k1_xboole_0,'#skF_4','#skF_5')
    | k1_relset_1('#skF_4','#skF_5',k1_xboole_0) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_7003,c_7336])).

tff(c_7348,plain,
    ( v1_funct_2(k1_xboole_0,'#skF_4','#skF_5')
    | k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6507,c_7339])).

tff(c_7352,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7348])).

tff(c_6248,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6244,c_68])).

tff(c_6481,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6248,c_6478])).

tff(c_6487,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5388,c_6481])).

tff(c_7397,plain,(
    ! [B_559,A_560,C_561] :
      ( k1_xboole_0 = B_559
      | k1_relset_1(A_560,B_559,C_561) = A_560
      | ~ v1_funct_2(C_561,A_560,B_559)
      | ~ m1_subset_1(C_561,k1_zfmisc_1(k2_zfmisc_1(A_560,B_559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_7403,plain,(
    ! [C_561] :
      ( k1_xboole_0 = '#skF_5'
      | k1_relset_1('#skF_4','#skF_5',C_561) = '#skF_4'
      | ~ v1_funct_2(C_561,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_561,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6244,c_7397])).

tff(c_7493,plain,(
    ! [C_570] :
      ( k1_relset_1('#skF_4','#skF_5',C_570) = '#skF_4'
      | ~ v1_funct_2(C_570,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_570,k1_zfmisc_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7403])).

tff(c_7499,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6248,c_7493])).

tff(c_7509,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6487,c_7499])).

tff(c_7511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7352,c_7509])).

tff(c_7513,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7348])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k1_xboole_0 = B_15
      | k1_xboole_0 = A_14
      | k2_zfmisc_1(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6253,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_6244,c_22])).

tff(c_6258,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6253])).

tff(c_6275,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_6258])).

tff(c_7558,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7513,c_6275])).

tff(c_7570,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_4',B_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7513,c_7513,c_26])).

tff(c_7852,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7570,c_6244])).

tff(c_7854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7558,c_7852])).

tff(c_7855,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6258])).

tff(c_7872,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7855,c_12])).

tff(c_7856,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6258])).

tff(c_7877,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7855,c_7856])).

tff(c_5451,plain,(
    ! [C_367,B_368,A_369] :
      ( ~ v1_xboole_0(C_367)
      | ~ m1_subset_1(B_368,k1_zfmisc_1(C_367))
      | ~ r2_hidden(A_369,B_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5457,plain,(
    ! [A_369] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_369,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_5451])).

tff(c_5466,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5457])).

tff(c_6246,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6244,c_5466])).

tff(c_7879,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7877,c_6246])).

tff(c_7906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7872,c_7879])).

tff(c_7909,plain,(
    ! [A_583] : ~ r2_hidden(A_583,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_5457])).

tff(c_7924,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_14,c_7909])).

tff(c_7948,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7924,c_82])).

tff(c_7922,plain,(
    ! [B_6] : r1_tarski('#skF_7',B_6) ),
    inference(resolution,[status(thm)],[c_10,c_7909])).

tff(c_7908,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5457])).

tff(c_8060,plain,(
    ! [A_591] :
      ( ~ v1_xboole_0(A_591)
      | A_591 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7924,c_116])).

tff(c_8070,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7908,c_8060])).

tff(c_8041,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_8086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7922,c_8070,c_8041])).

tff(c_8087,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_8380,plain,(
    ! [B_626,A_627] :
      ( B_626 = '#skF_7'
      | A_627 = '#skF_7'
      | k2_zfmisc_1(A_627,B_626) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7924,c_7924,c_7924,c_22])).

tff(c_8383,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8087,c_8380])).

tff(c_8392,plain,(
    '#skF_7' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_7948,c_8383])).

tff(c_8416,plain,(
    ! [B_6] : r1_tarski('#skF_4',B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8392,c_7922])).

tff(c_7937,plain,(
    k1_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7924,c_5388])).

tff(c_8417,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8392,c_8392,c_7937])).

tff(c_8184,plain,(
    ! [A_600,B_601,C_602] :
      ( k1_relset_1(A_600,B_601,C_602) = k1_relat_1(C_602)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9255,plain,(
    ! [A_711,B_712,A_713] :
      ( k1_relset_1(A_711,B_712,A_713) = k1_relat_1(A_713)
      | ~ r1_tarski(A_713,k2_zfmisc_1(A_711,B_712)) ) ),
    inference(resolution,[status(thm)],[c_30,c_8184])).

tff(c_9265,plain,(
    ! [A_711,B_712] : k1_relset_1(A_711,B_712,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8416,c_9255])).

tff(c_9275,plain,(
    ! [A_711,B_712] : k1_relset_1(A_711,B_712,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8417,c_9265])).

tff(c_8419,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8392,c_7924])).

tff(c_54,plain,(
    ! [C_39,B_38] :
      ( v1_funct_2(C_39,k1_xboole_0,B_38)
      | k1_relset_1(k1_xboole_0,B_38,C_39) != k1_xboole_0
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8430,plain,(
    ! [C_628,B_629] :
      ( v1_funct_2(C_628,k1_xboole_0,B_629)
      | k1_relset_1(k1_xboole_0,B_629,C_628) != k1_xboole_0
      | ~ m1_subset_1(C_628,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54])).

tff(c_8434,plain,(
    ! [A_16,B_629] :
      ( v1_funct_2(A_16,k1_xboole_0,B_629)
      | k1_relset_1(k1_xboole_0,B_629,A_16) != k1_xboole_0
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_8430])).

tff(c_9506,plain,(
    ! [A_747,B_748] :
      ( v1_funct_2(A_747,'#skF_4',B_748)
      | k1_relset_1('#skF_4',B_748,A_747) != '#skF_4'
      | ~ r1_tarski(A_747,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8419,c_8419,c_8419,c_8419,c_8434])).

tff(c_8423,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8392,c_150])).

tff(c_9509,plain,
    ( k1_relset_1('#skF_4','#skF_6','#skF_4') != '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_9506,c_8423])).

tff(c_9515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8416,c_9275,c_9509])).

tff(c_9516,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_10165,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_10148,c_9516])).

tff(c_10181,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9568,c_10022,c_10165])).

tff(c_10294,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10291,c_10181])).

tff(c_10299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_10294])).

tff(c_10300,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_10302,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10300,c_12])).

tff(c_10352,plain,(
    ! [A_855] :
      ( r2_hidden('#skF_3'(A_855),A_855)
      | A_855 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10300,c_14])).

tff(c_10358,plain,(
    ! [A_858] :
      ( ~ v1_xboole_0(A_858)
      | A_858 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10352,c_2])).

tff(c_10368,plain,(
    ! [A_859] :
      ( k1_relat_1(A_859) = '#skF_4'
      | ~ v1_xboole_0(A_859) ) ),
    inference(resolution,[status(thm)],[c_36,c_10358])).

tff(c_10376,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10302,c_10368])).

tff(c_10478,plain,(
    ! [A_873,B_874] :
      ( r2_hidden('#skF_2'(A_873,B_874),A_873)
      | r1_tarski(A_873,B_874) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10489,plain,(
    ! [A_875,B_876] :
      ( ~ v1_xboole_0(A_875)
      | r1_tarski(A_875,B_876) ) ),
    inference(resolution,[status(thm)],[c_10478,c_2])).

tff(c_10313,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10300,c_10300,c_24])).

tff(c_10301,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_10307,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10300,c_10301])).

tff(c_10342,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10313,c_10307,c_68])).

tff(c_10414,plain,(
    ! [A_861,B_862] :
      ( r1_tarski(A_861,B_862)
      | ~ m1_subset_1(A_861,k1_zfmisc_1(B_862)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10422,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_10342,c_10414])).

tff(c_10435,plain,(
    ! [B_867,A_868] :
      ( B_867 = A_868
      | ~ r1_tarski(B_867,A_868)
      | ~ r1_tarski(A_868,B_867) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10442,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_10422,c_10435])).

tff(c_10448,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10442])).

tff(c_10498,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_10489,c_10448])).

tff(c_10506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10302,c_10498])).

tff(c_10507,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10442])).

tff(c_10513,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10507,c_10342])).

tff(c_10323,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_4',B_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10300,c_10300,c_26])).

tff(c_11063,plain,(
    ! [A_955,B_956,C_957] :
      ( k1_relset_1(A_955,B_956,C_957) = k1_relat_1(C_957)
      | ~ m1_subset_1(C_957,k1_zfmisc_1(k2_zfmisc_1(A_955,B_956))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11075,plain,(
    ! [B_958,C_959] :
      ( k1_relset_1('#skF_4',B_958,C_959) = k1_relat_1(C_959)
      | ~ m1_subset_1(C_959,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10323,c_11063])).

tff(c_11077,plain,(
    ! [B_958] : k1_relset_1('#skF_4',B_958,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10513,c_11075])).

tff(c_11082,plain,(
    ! [B_958] : k1_relset_1('#skF_4',B_958,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10376,c_11077])).

tff(c_76,plain,(
    ! [C_39,B_38] :
      ( v1_funct_2(C_39,k1_xboole_0,B_38)
      | k1_relset_1(k1_xboole_0,B_38,C_39) != k1_xboole_0
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54])).

tff(c_11504,plain,(
    ! [C_993,B_994] :
      ( v1_funct_2(C_993,'#skF_4',B_994)
      | k1_relset_1('#skF_4',B_994,C_993) != '#skF_4'
      | ~ m1_subset_1(C_993,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10300,c_10300,c_10300,c_10300,c_76])).

tff(c_11506,plain,(
    ! [B_994] :
      ( v1_funct_2('#skF_4','#skF_4',B_994)
      | k1_relset_1('#skF_4',B_994,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10513,c_11504])).

tff(c_11512,plain,(
    ! [B_994] : v1_funct_2('#skF_4','#skF_4',B_994) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11082,c_11506])).

tff(c_10387,plain,(
    ~ v1_funct_2('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10342,c_10323,c_74])).

tff(c_10511,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10507,c_10387])).

tff(c_11517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_10511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:12:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.57/2.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/2.94  
% 8.78/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/2.95  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 8.78/2.95  
% 8.78/2.95  %Foreground sorts:
% 8.78/2.95  
% 8.78/2.95  
% 8.78/2.95  %Background operators:
% 8.78/2.95  
% 8.78/2.95  
% 8.78/2.95  %Foreground operators:
% 8.78/2.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.78/2.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.78/2.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.78/2.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.78/2.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.78/2.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.78/2.95  tff('#skF_7', type, '#skF_7': $i).
% 8.78/2.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.78/2.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.78/2.95  tff('#skF_5', type, '#skF_5': $i).
% 8.78/2.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.78/2.95  tff('#skF_6', type, '#skF_6': $i).
% 8.78/2.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.78/2.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.78/2.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.78/2.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.78/2.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.78/2.95  tff('#skF_4', type, '#skF_4': $i).
% 8.78/2.95  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.78/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.78/2.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.78/2.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.78/2.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.78/2.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.78/2.95  
% 8.78/2.98  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.78/2.98  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 8.78/2.98  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.78/2.98  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.78/2.98  tff(f_83, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.78/2.98  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.78/2.98  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.78/2.98  tff(f_105, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.78/2.98  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.78/2.98  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.78/2.98  tff(f_81, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 8.78/2.98  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.78/2.98  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.78/2.98  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.78/2.98  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.78/2.98  tff(f_70, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 8.78/2.98  tff(f_89, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 8.78/2.98  tff(c_20, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.78/2.98  tff(c_64, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.78/2.98  tff(c_82, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_64])).
% 8.78/2.98  tff(c_70, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.78/2.98  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.78/2.98  tff(c_9817, plain, (![A_793, B_794, C_795]: (k1_relset_1(A_793, B_794, C_795)=k1_relat_1(C_795) | ~m1_subset_1(C_795, k1_zfmisc_1(k2_zfmisc_1(A_793, B_794))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.78/2.98  tff(c_9832, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_9817])).
% 8.78/2.98  tff(c_10269, plain, (![B_846, A_847, C_848]: (k1_xboole_0=B_846 | k1_relset_1(A_847, B_846, C_848)=A_847 | ~v1_funct_2(C_848, A_847, B_846) | ~m1_subset_1(C_848, k1_zfmisc_1(k2_zfmisc_1(A_847, B_846))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.98  tff(c_10279, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_10269])).
% 8.78/2.98  tff(c_10290, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9832, c_10279])).
% 8.78/2.98  tff(c_10291, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_82, c_10290])).
% 8.78/2.98  tff(c_38, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.78/2.98  tff(c_9558, plain, (![B_754, A_755]: (v1_relat_1(B_754) | ~m1_subset_1(B_754, k1_zfmisc_1(A_755)) | ~v1_relat_1(A_755))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.78/2.98  tff(c_9564, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_9558])).
% 8.78/2.98  tff(c_9568, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_9564])).
% 8.78/2.98  tff(c_9934, plain, (![A_806, B_807, C_808]: (k2_relset_1(A_806, B_807, C_808)=k2_relat_1(C_808) | ~m1_subset_1(C_808, k1_zfmisc_1(k2_zfmisc_1(A_806, B_807))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.78/2.98  tff(c_9949, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_9934])).
% 8.78/2.98  tff(c_66, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.78/2.98  tff(c_10022, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9949, c_66])).
% 8.78/2.98  tff(c_10148, plain, (![C_830, A_831, B_832]: (m1_subset_1(C_830, k1_zfmisc_1(k2_zfmisc_1(A_831, B_832))) | ~r1_tarski(k2_relat_1(C_830), B_832) | ~r1_tarski(k1_relat_1(C_830), A_831) | ~v1_relat_1(C_830))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.78/2.98  tff(c_14, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.78/2.98  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.78/2.98  tff(c_36, plain, (![A_24]: (v1_xboole_0(k1_relat_1(A_24)) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.78/2.98  tff(c_112, plain, (![A_48]: (r2_hidden('#skF_3'(A_48), A_48) | k1_xboole_0=A_48)), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.78/2.98  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/2.98  tff(c_117, plain, (![A_49]: (~v1_xboole_0(A_49) | k1_xboole_0=A_49)), inference(resolution, [status(thm)], [c_112, c_2])).
% 8.78/2.98  tff(c_132, plain, (![A_51]: (k1_relat_1(A_51)=k1_xboole_0 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_36, c_117])).
% 8.78/2.98  tff(c_140, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_132])).
% 8.78/2.98  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.78/2.98  tff(c_30, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.78/2.98  tff(c_24, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.78/2.98  tff(c_50, plain, (![A_37]: (v1_funct_2(k1_xboole_0, A_37, k1_xboole_0) | k1_xboole_0=A_37 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_37, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.98  tff(c_77, plain, (![A_37]: (v1_funct_2(k1_xboole_0, A_37, k1_xboole_0) | k1_xboole_0=A_37 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_50])).
% 8.78/2.98  tff(c_6300, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_77])).
% 8.78/2.98  tff(c_6303, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_6300])).
% 8.78/2.98  tff(c_6307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_6303])).
% 8.78/2.98  tff(c_6309, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_77])).
% 8.78/2.98  tff(c_32, plain, (![C_20, B_19, A_18]: (~v1_xboole_0(C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.78/2.98  tff(c_6311, plain, (![A_18]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_6309, c_32])).
% 8.78/2.98  tff(c_6326, plain, (![A_459]: (~r2_hidden(A_459, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6311])).
% 8.78/2.98  tff(c_6339, plain, (![B_6]: (r1_tarski(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_10, c_6326])).
% 8.78/2.98  tff(c_199, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.78/2.98  tff(c_205, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_199])).
% 8.78/2.98  tff(c_209, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_205])).
% 8.78/2.98  tff(c_239, plain, (![A_67]: (k1_relat_1(A_67)=k1_xboole_0 | k2_relat_1(A_67)!=k1_xboole_0 | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.78/2.98  tff(c_249, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_209, c_239])).
% 8.78/2.98  tff(c_253, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_249])).
% 8.78/2.98  tff(c_722, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.78/2.98  tff(c_737, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_722])).
% 8.78/2.98  tff(c_1030, plain, (![B_172, A_173, C_174]: (k1_xboole_0=B_172 | k1_relset_1(A_173, B_172, C_174)=A_173 | ~v1_funct_2(C_174, A_173, B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.98  tff(c_1040, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_1030])).
% 8.78/2.98  tff(c_1051, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_737, c_1040])).
% 8.78/2.98  tff(c_1052, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_82, c_1051])).
% 8.78/2.98  tff(c_544, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.78/2.98  tff(c_559, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_544])).
% 8.78/2.98  tff(c_632, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_66])).
% 8.78/2.98  tff(c_766, plain, (![C_134, A_135, B_136]: (m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~r1_tarski(k2_relat_1(C_134), B_136) | ~r1_tarski(k1_relat_1(C_134), A_135) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.78/2.98  tff(c_28, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.78/2.98  tff(c_2496, plain, (![C_246, A_247, B_248]: (r1_tarski(C_246, k2_zfmisc_1(A_247, B_248)) | ~r1_tarski(k2_relat_1(C_246), B_248) | ~r1_tarski(k1_relat_1(C_246), A_247) | ~v1_relat_1(C_246))), inference(resolution, [status(thm)], [c_766, c_28])).
% 8.78/2.98  tff(c_2504, plain, (![A_247]: (r1_tarski('#skF_7', k2_zfmisc_1(A_247, '#skF_6')) | ~r1_tarski(k1_relat_1('#skF_7'), A_247) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_632, c_2496])).
% 8.78/2.98  tff(c_2526, plain, (![A_249]: (r1_tarski('#skF_7', k2_zfmisc_1(A_249, '#skF_6')) | ~r1_tarski('#skF_4', A_249))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_1052, c_2504])).
% 8.78/2.98  tff(c_736, plain, (![A_127, B_128, A_16]: (k1_relset_1(A_127, B_128, A_16)=k1_relat_1(A_16) | ~r1_tarski(A_16, k2_zfmisc_1(A_127, B_128)))), inference(resolution, [status(thm)], [c_30, c_722])).
% 8.78/2.98  tff(c_2534, plain, (![A_249]: (k1_relset_1(A_249, '#skF_6', '#skF_7')=k1_relat_1('#skF_7') | ~r1_tarski('#skF_4', A_249))), inference(resolution, [status(thm)], [c_2526, c_736])).
% 8.78/2.98  tff(c_2582, plain, (![A_251]: (k1_relset_1(A_251, '#skF_6', '#skF_7')='#skF_4' | ~r1_tarski('#skF_4', A_251))), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_2534])).
% 8.78/2.98  tff(c_2592, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_7')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_2582])).
% 8.78/2.98  tff(c_48, plain, (![C_36, A_34, B_35]: (m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~r1_tarski(k2_relat_1(C_36), B_35) | ~r1_tarski(k1_relat_1(C_36), A_34) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.78/2.98  tff(c_887, plain, (![B_152, C_153, A_154]: (k1_xboole_0=B_152 | v1_funct_2(C_153, A_154, B_152) | k1_relset_1(A_154, B_152, C_153)!=A_154 | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_152))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.98  tff(c_4449, plain, (![B_327, C_328, A_329]: (k1_xboole_0=B_327 | v1_funct_2(C_328, A_329, B_327) | k1_relset_1(A_329, B_327, C_328)!=A_329 | ~r1_tarski(k2_relat_1(C_328), B_327) | ~r1_tarski(k1_relat_1(C_328), A_329) | ~v1_relat_1(C_328))), inference(resolution, [status(thm)], [c_48, c_887])).
% 8.78/2.98  tff(c_4457, plain, (![A_329]: (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', A_329, '#skF_6') | k1_relset_1(A_329, '#skF_6', '#skF_7')!=A_329 | ~r1_tarski(k1_relat_1('#skF_7'), A_329) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_632, c_4449])).
% 8.78/2.98  tff(c_4474, plain, (![A_329]: (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', A_329, '#skF_6') | k1_relset_1(A_329, '#skF_6', '#skF_7')!=A_329 | ~r1_tarski('#skF_4', A_329))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_1052, c_4457])).
% 8.78/2.98  tff(c_5129, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_4474])).
% 8.78/2.98  tff(c_429, plain, (![C_94, B_95, A_96]: (r2_hidden(C_94, B_95) | ~r2_hidden(C_94, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.78/2.98  tff(c_471, plain, (![A_104, B_105]: (r2_hidden('#skF_3'(A_104), B_105) | ~r1_tarski(A_104, B_105) | k1_xboole_0=A_104)), inference(resolution, [status(thm)], [c_14, c_429])).
% 8.78/2.98  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.78/2.98  tff(c_4394, plain, (![A_322, B_323, B_324]: (r2_hidden('#skF_3'(A_322), B_323) | ~r1_tarski(B_324, B_323) | ~r1_tarski(A_322, B_324) | k1_xboole_0=A_322)), inference(resolution, [status(thm)], [c_471, c_6])).
% 8.78/2.98  tff(c_4419, plain, (![A_325]: (r2_hidden('#skF_3'(A_325), '#skF_6') | ~r1_tarski(A_325, k2_relat_1('#skF_7')) | k1_xboole_0=A_325)), inference(resolution, [status(thm)], [c_632, c_4394])).
% 8.78/2.98  tff(c_4690, plain, (![A_336, B_337]: (r2_hidden('#skF_3'(A_336), B_337) | ~r1_tarski('#skF_6', B_337) | ~r1_tarski(A_336, k2_relat_1('#skF_7')) | k1_xboole_0=A_336)), inference(resolution, [status(thm)], [c_4419, c_6])).
% 8.78/2.98  tff(c_490, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_77])).
% 8.78/2.98  tff(c_493, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_490])).
% 8.78/2.98  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_493])).
% 8.78/2.98  tff(c_499, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_77])).
% 8.78/2.98  tff(c_501, plain, (![A_18]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_499, c_32])).
% 8.78/2.98  tff(c_510, plain, (![A_18]: (~r2_hidden(A_18, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_501])).
% 8.78/2.98  tff(c_4710, plain, (![A_336]: (~r1_tarski('#skF_6', k1_xboole_0) | ~r1_tarski(A_336, k2_relat_1('#skF_7')) | k1_xboole_0=A_336)), inference(resolution, [status(thm)], [c_4690, c_510])).
% 8.78/2.98  tff(c_4714, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4710])).
% 8.78/2.98  tff(c_5134, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5129, c_4714])).
% 8.78/2.98  tff(c_5210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_5134])).
% 8.78/2.98  tff(c_5213, plain, (![A_357]: (v1_funct_2('#skF_7', A_357, '#skF_6') | k1_relset_1(A_357, '#skF_6', '#skF_7')!=A_357 | ~r1_tarski('#skF_4', A_357))), inference(splitRight, [status(thm)], [c_4474])).
% 8.78/2.98  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.78/2.98  tff(c_62, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_4', '#skF_6') | ~v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.78/2.98  tff(c_74, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62])).
% 8.78/2.98  tff(c_150, plain, (~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_74])).
% 8.78/2.98  tff(c_5221, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_7')!='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_5213, c_150])).
% 8.78/2.98  tff(c_5230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_2592, c_5221])).
% 8.78/2.98  tff(c_5232, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4710])).
% 8.78/2.98  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/2.98  tff(c_460, plain, (![A_102, B_103]: (r2_hidden('#skF_1'(A_102), B_103) | ~r1_tarski(A_102, B_103) | v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_4, c_429])).
% 8.78/2.98  tff(c_4284, plain, (![A_312, B_313, B_314]: (r2_hidden('#skF_1'(A_312), B_313) | ~r1_tarski(B_314, B_313) | ~r1_tarski(A_312, B_314) | v1_xboole_0(A_312))), inference(resolution, [status(thm)], [c_460, c_6])).
% 8.78/2.98  tff(c_4309, plain, (![A_315]: (r2_hidden('#skF_1'(A_315), '#skF_6') | ~r1_tarski(A_315, k2_relat_1('#skF_7')) | v1_xboole_0(A_315))), inference(resolution, [status(thm)], [c_632, c_4284])).
% 8.78/2.98  tff(c_378, plain, (![C_84, B_85, A_86]: (~v1_xboole_0(C_84) | ~m1_subset_1(B_85, k1_zfmisc_1(C_84)) | ~r2_hidden(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.78/2.98  tff(c_383, plain, (![B_17, A_86, A_16]: (~v1_xboole_0(B_17) | ~r2_hidden(A_86, A_16) | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_30, c_378])).
% 8.78/2.98  tff(c_4321, plain, (![B_17, A_315]: (~v1_xboole_0(B_17) | ~r1_tarski('#skF_6', B_17) | ~r1_tarski(A_315, k2_relat_1('#skF_7')) | v1_xboole_0(A_315))), inference(resolution, [status(thm)], [c_4309, c_383])).
% 8.78/2.98  tff(c_4370, plain, (![B_17]: (~v1_xboole_0(B_17) | ~r1_tarski('#skF_6', B_17))), inference(splitLeft, [status(thm)], [c_4321])).
% 8.78/2.98  tff(c_5237, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_5232, c_4370])).
% 8.78/2.98  tff(c_5284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_5237])).
% 8.78/2.98  tff(c_5286, plain, (![A_358]: (~r1_tarski(A_358, k2_relat_1('#skF_7')) | v1_xboole_0(A_358))), inference(splitRight, [status(thm)], [c_4321])).
% 8.78/2.98  tff(c_5312, plain, (v1_xboole_0(k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_20, c_5286])).
% 8.78/2.98  tff(c_116, plain, (![A_48]: (~v1_xboole_0(A_48) | k1_xboole_0=A_48)), inference(resolution, [status(thm)], [c_112, c_2])).
% 8.78/2.98  tff(c_5371, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_5312, c_116])).
% 8.78/2.98  tff(c_5387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_5371])).
% 8.78/2.98  tff(c_5388, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_249])).
% 8.78/2.98  tff(c_5787, plain, (![A_407, B_408, C_409]: (k1_relset_1(A_407, B_408, C_409)=k1_relat_1(C_409) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(A_407, B_408))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.78/2.98  tff(c_5794, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_5787])).
% 8.78/2.98  tff(c_5803, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5388, c_5794])).
% 8.78/2.98  tff(c_6020, plain, (![B_443, A_444, C_445]: (k1_xboole_0=B_443 | k1_relset_1(A_444, B_443, C_445)=A_444 | ~v1_funct_2(C_445, A_444, B_443) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_444, B_443))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.98  tff(c_6030, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_6020])).
% 8.78/2.98  tff(c_6041, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5803, c_6030])).
% 8.78/2.98  tff(c_6042, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_82, c_6041])).
% 8.78/2.98  tff(c_5622, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_77])).
% 8.78/2.98  tff(c_5625, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_5622])).
% 8.78/2.98  tff(c_5629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_5625])).
% 8.78/2.98  tff(c_5631, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_77])).
% 8.78/2.98  tff(c_5633, plain, (![A_18]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_5631, c_32])).
% 8.78/2.98  tff(c_5648, plain, (![A_395]: (~r2_hidden(A_395, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_5633])).
% 8.78/2.98  tff(c_5666, plain, (![B_6]: (r1_tarski(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_10, c_5648])).
% 8.78/2.98  tff(c_6068, plain, (![B_6]: (r1_tarski('#skF_4', B_6))), inference(demodulation, [status(thm), theory('equality')], [c_6042, c_5666])).
% 8.78/2.98  tff(c_26, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.78/2.98  tff(c_6084, plain, (![B_15]: (k2_zfmisc_1('#skF_4', B_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6042, c_6042, c_26])).
% 8.78/2.98  tff(c_178, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.78/2.98  tff(c_186, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_178])).
% 8.78/2.98  tff(c_210, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.78/2.98  tff(c_217, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_186, c_210])).
% 8.78/2.98  tff(c_5568, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_217])).
% 8.78/2.98  tff(c_6237, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6084, c_5568])).
% 8.78/2.98  tff(c_6243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6068, c_6237])).
% 8.78/2.98  tff(c_6244, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_217])).
% 8.78/2.98  tff(c_6344, plain, (![A_460, B_461, C_462]: (k1_relset_1(A_460, B_461, C_462)=k1_relat_1(C_462) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.78/2.98  tff(c_6478, plain, (![C_477]: (k1_relset_1('#skF_4', '#skF_5', C_477)=k1_relat_1(C_477) | ~m1_subset_1(C_477, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_6244, c_6344])).
% 8.78/2.98  tff(c_6493, plain, (![A_478]: (k1_relset_1('#skF_4', '#skF_5', A_478)=k1_relat_1(A_478) | ~r1_tarski(A_478, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_6478])).
% 8.78/2.98  tff(c_6497, plain, (k1_relset_1('#skF_4', '#skF_5', k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6339, c_6493])).
% 8.78/2.98  tff(c_6507, plain, (k1_relset_1('#skF_4', '#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_6497])).
% 8.78/2.98  tff(c_83, plain, (![A_43]: (k2_zfmisc_1(A_43, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.78/2.98  tff(c_87, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_83, c_38])).
% 8.78/2.98  tff(c_5407, plain, (![A_362]: (k2_relat_1(A_362)=k1_xboole_0 | k1_relat_1(A_362)!=k1_xboole_0 | ~v1_relat_1(A_362))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.78/2.98  tff(c_5413, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_5407])).
% 8.78/2.98  tff(c_5422, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_5413])).
% 8.78/2.98  tff(c_6895, plain, (![C_528, A_529, B_530]: (m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))) | ~r1_tarski(k2_relat_1(C_528), B_530) | ~r1_tarski(k1_relat_1(C_528), A_529) | ~v1_relat_1(C_528))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.78/2.98  tff(c_6981, plain, (![C_537]: (m1_subset_1(C_537, k1_zfmisc_1('#skF_7')) | ~r1_tarski(k2_relat_1(C_537), '#skF_5') | ~r1_tarski(k1_relat_1(C_537), '#skF_4') | ~v1_relat_1(C_537))), inference(superposition, [status(thm), theory('equality')], [c_6244, c_6895])).
% 8.78/2.98  tff(c_6993, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_7')) | ~r1_tarski(k1_xboole_0, '#skF_5') | ~r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5422, c_6981])).
% 8.78/2.98  tff(c_7003, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_6339, c_140, c_6339, c_6993])).
% 8.78/2.98  tff(c_7156, plain, (![B_545, C_546, A_547]: (k1_xboole_0=B_545 | v1_funct_2(C_546, A_547, B_545) | k1_relset_1(A_547, B_545, C_546)!=A_547 | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(A_547, B_545))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.98  tff(c_7162, plain, (![C_546]: (k1_xboole_0='#skF_5' | v1_funct_2(C_546, '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', C_546)!='#skF_4' | ~m1_subset_1(C_546, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_6244, c_7156])).
% 8.78/2.98  tff(c_7336, plain, (![C_550]: (v1_funct_2(C_550, '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', C_550)!='#skF_4' | ~m1_subset_1(C_550, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_82, c_7162])).
% 8.78/2.98  tff(c_7339, plain, (v1_funct_2(k1_xboole_0, '#skF_4', '#skF_5') | k1_relset_1('#skF_4', '#skF_5', k1_xboole_0)!='#skF_4'), inference(resolution, [status(thm)], [c_7003, c_7336])).
% 8.78/2.98  tff(c_7348, plain, (v1_funct_2(k1_xboole_0, '#skF_4', '#skF_5') | k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6507, c_7339])).
% 8.78/2.98  tff(c_7352, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_7348])).
% 8.78/2.98  tff(c_6248, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6244, c_68])).
% 8.78/2.98  tff(c_6481, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6248, c_6478])).
% 8.78/2.98  tff(c_6487, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5388, c_6481])).
% 8.78/2.98  tff(c_7397, plain, (![B_559, A_560, C_561]: (k1_xboole_0=B_559 | k1_relset_1(A_560, B_559, C_561)=A_560 | ~v1_funct_2(C_561, A_560, B_559) | ~m1_subset_1(C_561, k1_zfmisc_1(k2_zfmisc_1(A_560, B_559))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.98  tff(c_7403, plain, (![C_561]: (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', C_561)='#skF_4' | ~v1_funct_2(C_561, '#skF_4', '#skF_5') | ~m1_subset_1(C_561, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_6244, c_7397])).
% 8.78/2.98  tff(c_7493, plain, (![C_570]: (k1_relset_1('#skF_4', '#skF_5', C_570)='#skF_4' | ~v1_funct_2(C_570, '#skF_4', '#skF_5') | ~m1_subset_1(C_570, k1_zfmisc_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_82, c_7403])).
% 8.78/2.98  tff(c_7499, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6248, c_7493])).
% 8.78/2.98  tff(c_7509, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6487, c_7499])).
% 8.78/2.98  tff(c_7511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7352, c_7509])).
% 8.78/2.98  tff(c_7513, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_7348])).
% 8.78/2.98  tff(c_22, plain, (![B_15, A_14]: (k1_xboole_0=B_15 | k1_xboole_0=A_14 | k2_zfmisc_1(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.78/2.98  tff(c_6253, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_6244, c_22])).
% 8.78/2.98  tff(c_6258, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_82, c_6253])).
% 8.78/2.98  tff(c_6275, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_6258])).
% 8.78/2.98  tff(c_7558, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7513, c_6275])).
% 8.78/2.98  tff(c_7570, plain, (![B_15]: (k2_zfmisc_1('#skF_4', B_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7513, c_7513, c_26])).
% 8.78/2.98  tff(c_7852, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7570, c_6244])).
% 8.78/2.98  tff(c_7854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7558, c_7852])).
% 8.78/2.98  tff(c_7855, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_6258])).
% 8.78/2.98  tff(c_7872, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7855, c_12])).
% 8.78/2.98  tff(c_7856, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6258])).
% 8.78/2.98  tff(c_7877, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7855, c_7856])).
% 8.78/2.98  tff(c_5451, plain, (![C_367, B_368, A_369]: (~v1_xboole_0(C_367) | ~m1_subset_1(B_368, k1_zfmisc_1(C_367)) | ~r2_hidden(A_369, B_368))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.78/2.98  tff(c_5457, plain, (![A_369]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_369, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_5451])).
% 8.78/2.98  tff(c_5466, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_5457])).
% 8.78/2.98  tff(c_6246, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6244, c_5466])).
% 8.78/2.98  tff(c_7879, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7877, c_6246])).
% 8.78/2.98  tff(c_7906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7872, c_7879])).
% 8.78/2.98  tff(c_7909, plain, (![A_583]: (~r2_hidden(A_583, '#skF_7'))), inference(splitRight, [status(thm)], [c_5457])).
% 8.78/2.98  tff(c_7924, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_14, c_7909])).
% 8.78/2.98  tff(c_7948, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_7924, c_82])).
% 8.78/2.98  tff(c_7922, plain, (![B_6]: (r1_tarski('#skF_7', B_6))), inference(resolution, [status(thm)], [c_10, c_7909])).
% 8.78/2.98  tff(c_7908, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_5457])).
% 8.78/2.98  tff(c_8060, plain, (![A_591]: (~v1_xboole_0(A_591) | A_591='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7924, c_116])).
% 8.78/2.98  tff(c_8070, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_7908, c_8060])).
% 8.78/2.98  tff(c_8041, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_217])).
% 8.78/2.98  tff(c_8086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7922, c_8070, c_8041])).
% 8.78/2.98  tff(c_8087, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_217])).
% 8.78/2.98  tff(c_8380, plain, (![B_626, A_627]: (B_626='#skF_7' | A_627='#skF_7' | k2_zfmisc_1(A_627, B_626)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7924, c_7924, c_7924, c_22])).
% 8.78/2.98  tff(c_8383, plain, ('#skF_7'='#skF_5' | '#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8087, c_8380])).
% 8.78/2.98  tff(c_8392, plain, ('#skF_7'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_7948, c_8383])).
% 8.78/2.98  tff(c_8416, plain, (![B_6]: (r1_tarski('#skF_4', B_6))), inference(demodulation, [status(thm), theory('equality')], [c_8392, c_7922])).
% 8.78/2.98  tff(c_7937, plain, (k1_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7924, c_5388])).
% 8.78/2.98  tff(c_8417, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8392, c_8392, c_7937])).
% 8.78/2.98  tff(c_8184, plain, (![A_600, B_601, C_602]: (k1_relset_1(A_600, B_601, C_602)=k1_relat_1(C_602) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.78/2.98  tff(c_9255, plain, (![A_711, B_712, A_713]: (k1_relset_1(A_711, B_712, A_713)=k1_relat_1(A_713) | ~r1_tarski(A_713, k2_zfmisc_1(A_711, B_712)))), inference(resolution, [status(thm)], [c_30, c_8184])).
% 8.78/2.98  tff(c_9265, plain, (![A_711, B_712]: (k1_relset_1(A_711, B_712, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8416, c_9255])).
% 8.78/2.98  tff(c_9275, plain, (![A_711, B_712]: (k1_relset_1(A_711, B_712, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8417, c_9265])).
% 8.78/2.98  tff(c_8419, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8392, c_7924])).
% 8.78/2.98  tff(c_54, plain, (![C_39, B_38]: (v1_funct_2(C_39, k1_xboole_0, B_38) | k1_relset_1(k1_xboole_0, B_38, C_39)!=k1_xboole_0 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_38))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.78/2.98  tff(c_8430, plain, (![C_628, B_629]: (v1_funct_2(C_628, k1_xboole_0, B_629) | k1_relset_1(k1_xboole_0, B_629, C_628)!=k1_xboole_0 | ~m1_subset_1(C_628, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54])).
% 8.78/2.98  tff(c_8434, plain, (![A_16, B_629]: (v1_funct_2(A_16, k1_xboole_0, B_629) | k1_relset_1(k1_xboole_0, B_629, A_16)!=k1_xboole_0 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_8430])).
% 8.78/2.98  tff(c_9506, plain, (![A_747, B_748]: (v1_funct_2(A_747, '#skF_4', B_748) | k1_relset_1('#skF_4', B_748, A_747)!='#skF_4' | ~r1_tarski(A_747, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8419, c_8419, c_8419, c_8419, c_8434])).
% 8.78/2.98  tff(c_8423, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8392, c_150])).
% 8.78/2.98  tff(c_9509, plain, (k1_relset_1('#skF_4', '#skF_6', '#skF_4')!='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_9506, c_8423])).
% 8.78/2.98  tff(c_9515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8416, c_9275, c_9509])).
% 8.78/2.98  tff(c_9516, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_74])).
% 8.78/2.98  tff(c_10165, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r1_tarski(k1_relat_1('#skF_7'), '#skF_4') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_10148, c_9516])).
% 8.78/2.98  tff(c_10181, plain, (~r1_tarski(k1_relat_1('#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9568, c_10022, c_10165])).
% 8.78/2.98  tff(c_10294, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10291, c_10181])).
% 8.78/2.98  tff(c_10299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_10294])).
% 8.78/2.98  tff(c_10300, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_64])).
% 8.78/2.98  tff(c_10302, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10300, c_12])).
% 8.78/2.98  tff(c_10352, plain, (![A_855]: (r2_hidden('#skF_3'(A_855), A_855) | A_855='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10300, c_14])).
% 8.78/2.98  tff(c_10358, plain, (![A_858]: (~v1_xboole_0(A_858) | A_858='#skF_4')), inference(resolution, [status(thm)], [c_10352, c_2])).
% 8.78/2.98  tff(c_10368, plain, (![A_859]: (k1_relat_1(A_859)='#skF_4' | ~v1_xboole_0(A_859))), inference(resolution, [status(thm)], [c_36, c_10358])).
% 8.78/2.98  tff(c_10376, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_10302, c_10368])).
% 8.78/2.98  tff(c_10478, plain, (![A_873, B_874]: (r2_hidden('#skF_2'(A_873, B_874), A_873) | r1_tarski(A_873, B_874))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.78/2.98  tff(c_10489, plain, (![A_875, B_876]: (~v1_xboole_0(A_875) | r1_tarski(A_875, B_876))), inference(resolution, [status(thm)], [c_10478, c_2])).
% 8.78/2.98  tff(c_10313, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10300, c_10300, c_24])).
% 8.78/2.98  tff(c_10301, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 8.78/2.98  tff(c_10307, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10300, c_10301])).
% 8.78/2.98  tff(c_10342, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10313, c_10307, c_68])).
% 8.78/2.98  tff(c_10414, plain, (![A_861, B_862]: (r1_tarski(A_861, B_862) | ~m1_subset_1(A_861, k1_zfmisc_1(B_862)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.78/2.98  tff(c_10422, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_10342, c_10414])).
% 8.78/2.98  tff(c_10435, plain, (![B_867, A_868]: (B_867=A_868 | ~r1_tarski(B_867, A_868) | ~r1_tarski(A_868, B_867))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.78/2.98  tff(c_10442, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_10422, c_10435])).
% 8.78/2.98  tff(c_10448, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_10442])).
% 8.78/2.98  tff(c_10498, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_10489, c_10448])).
% 8.78/2.98  tff(c_10506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10302, c_10498])).
% 8.78/2.98  tff(c_10507, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_10442])).
% 8.78/2.98  tff(c_10513, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10507, c_10342])).
% 8.78/2.98  tff(c_10323, plain, (![B_15]: (k2_zfmisc_1('#skF_4', B_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10300, c_10300, c_26])).
% 8.78/2.98  tff(c_11063, plain, (![A_955, B_956, C_957]: (k1_relset_1(A_955, B_956, C_957)=k1_relat_1(C_957) | ~m1_subset_1(C_957, k1_zfmisc_1(k2_zfmisc_1(A_955, B_956))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.78/2.98  tff(c_11075, plain, (![B_958, C_959]: (k1_relset_1('#skF_4', B_958, C_959)=k1_relat_1(C_959) | ~m1_subset_1(C_959, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10323, c_11063])).
% 8.78/2.98  tff(c_11077, plain, (![B_958]: (k1_relset_1('#skF_4', B_958, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10513, c_11075])).
% 8.78/2.98  tff(c_11082, plain, (![B_958]: (k1_relset_1('#skF_4', B_958, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10376, c_11077])).
% 8.78/2.98  tff(c_76, plain, (![C_39, B_38]: (v1_funct_2(C_39, k1_xboole_0, B_38) | k1_relset_1(k1_xboole_0, B_38, C_39)!=k1_xboole_0 | ~m1_subset_1(C_39, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54])).
% 8.78/2.98  tff(c_11504, plain, (![C_993, B_994]: (v1_funct_2(C_993, '#skF_4', B_994) | k1_relset_1('#skF_4', B_994, C_993)!='#skF_4' | ~m1_subset_1(C_993, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10300, c_10300, c_10300, c_10300, c_76])).
% 8.78/2.98  tff(c_11506, plain, (![B_994]: (v1_funct_2('#skF_4', '#skF_4', B_994) | k1_relset_1('#skF_4', B_994, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_10513, c_11504])).
% 8.78/2.98  tff(c_11512, plain, (![B_994]: (v1_funct_2('#skF_4', '#skF_4', B_994))), inference(demodulation, [status(thm), theory('equality')], [c_11082, c_11506])).
% 8.78/2.98  tff(c_10387, plain, (~v1_funct_2('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10342, c_10323, c_74])).
% 8.78/2.98  tff(c_10511, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10507, c_10387])).
% 8.78/2.98  tff(c_11517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11512, c_10511])).
% 8.78/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/2.98  
% 8.78/2.98  Inference rules
% 8.78/2.98  ----------------------
% 8.78/2.98  #Ref     : 0
% 8.78/2.98  #Sup     : 2687
% 8.78/2.98  #Fact    : 0
% 8.78/2.98  #Define  : 0
% 8.78/2.98  #Split   : 43
% 8.78/2.98  #Chain   : 0
% 8.78/2.98  #Close   : 0
% 8.78/2.98  
% 8.78/2.98  Ordering : KBO
% 8.78/2.98  
% 8.78/2.98  Simplification rules
% 8.78/2.98  ----------------------
% 8.78/2.98  #Subsume      : 784
% 8.78/2.98  #Demod        : 2010
% 8.78/2.98  #Tautology    : 969
% 8.78/2.98  #SimpNegUnit  : 48
% 8.78/2.98  #BackRed      : 307
% 8.78/2.98  
% 8.78/2.98  #Partial instantiations: 0
% 8.78/2.98  #Strategies tried      : 1
% 8.78/2.98  
% 8.78/2.98  Timing (in seconds)
% 8.78/2.98  ----------------------
% 8.78/2.99  Preprocessing        : 0.34
% 8.78/2.99  Parsing              : 0.18
% 8.78/2.99  CNF conversion       : 0.02
% 8.78/2.99  Main loop            : 1.83
% 8.78/2.99  Inferencing          : 0.54
% 8.78/2.99  Reduction            : 0.57
% 8.78/2.99  Demodulation         : 0.39
% 8.78/2.99  BG Simplification    : 0.06
% 8.78/2.99  Subsumption          : 0.50
% 8.78/2.99  Abstraction          : 0.07
% 8.78/2.99  MUC search           : 0.00
% 8.78/2.99  Cooper               : 0.00
% 8.78/2.99  Total                : 2.25
% 8.78/2.99  Index Insertion      : 0.00
% 8.78/2.99  Index Deletion       : 0.00
% 8.78/2.99  Index Matching       : 0.00
% 8.78/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
