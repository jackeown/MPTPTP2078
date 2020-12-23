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
% DateTime   : Thu Dec  3 10:18:08 EST 2020

% Result     : Theorem 6.24s
% Output     : CNFRefutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 613 expanded)
%              Number of leaves         :   39 ( 229 expanded)
%              Depth                    :   19
%              Number of atoms          :  189 (1959 expanded)
%              Number of equality atoms :   27 ( 347 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_152,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_161,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_24,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_114,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_120,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_114])).

tff(c_124,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_120])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_508,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_517,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_508])).

tff(c_60,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_518,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_60])).

tff(c_528,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_518])).

tff(c_534,plain,(
    ~ v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_528])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_572,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_581,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_572])).

tff(c_1493,plain,(
    ! [B_203,A_204,C_205] :
      ( k1_xboole_0 = B_203
      | k1_relset_1(A_204,B_203,C_205) = A_204
      | ~ v1_funct_2(C_205,A_204,B_203)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1500,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1493])).

tff(c_1504,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_581,c_1500])).

tff(c_1505,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1504])).

tff(c_2210,plain,(
    ! [C_252,B_253] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_252),B_253,C_252),k1_relat_1(C_252))
      | m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_252),B_253)))
      | ~ v1_funct_1(C_252)
      | ~ v1_relat_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2219,plain,(
    ! [B_253] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_253,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_253)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_2210])).

tff(c_2658,plain,(
    ! [B_291] :
      ( r2_hidden('#skF_1'('#skF_3',B_291,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_291))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_1505,c_1505,c_2219])).

tff(c_26,plain,(
    ! [C_20,B_19,A_18] :
      ( v5_relat_1(C_20,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2703,plain,(
    ! [B_292] :
      ( v5_relat_1('#skF_5',B_292)
      | r2_hidden('#skF_1'('#skF_3',B_292,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2658,c_26])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2707,plain,(
    ! [B_292] :
      ( m1_subset_1('#skF_1'('#skF_3',B_292,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_292) ) ),
    inference(resolution,[status(thm)],[c_2703,c_12])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2708,plain,(
    ! [B_293] :
      ( m1_subset_1('#skF_1'('#skF_3',B_293,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_293) ) ),
    inference(resolution,[status(thm)],[c_2703,c_12])).

tff(c_46,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k3_funct_2(A_30,B_31,C_32,D_33) = k1_funct_1(C_32,D_33)
      | ~ m1_subset_1(D_33,A_30)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2710,plain,(
    ! [B_31,C_32,B_293] :
      ( k3_funct_2('#skF_3',B_31,C_32,'#skF_1'('#skF_3',B_293,'#skF_5')) = k1_funct_1(C_32,'#skF_1'('#skF_3',B_293,'#skF_5'))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_31)))
      | ~ v1_funct_2(C_32,'#skF_3',B_31)
      | ~ v1_funct_1(C_32)
      | v1_xboole_0('#skF_3')
      | v5_relat_1('#skF_5',B_293) ) ),
    inference(resolution,[status(thm)],[c_2708,c_46])).

tff(c_2714,plain,(
    ! [B_294,C_295,B_296] :
      ( k3_funct_2('#skF_3',B_294,C_295,'#skF_1'('#skF_3',B_296,'#skF_5')) = k1_funct_1(C_295,'#skF_1'('#skF_3',B_296,'#skF_5'))
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_294)))
      | ~ v1_funct_2(C_295,'#skF_3',B_294)
      | ~ v1_funct_1(C_295)
      | v5_relat_1('#skF_5',B_296) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2710])).

tff(c_2721,plain,(
    ! [B_296] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_296,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_296,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v5_relat_1('#skF_5',B_296) ) ),
    inference(resolution,[status(thm)],[c_64,c_2714])).

tff(c_4667,plain,(
    ! [B_376] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_376,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_376,'#skF_5'))
      | v5_relat_1('#skF_5',B_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2721])).

tff(c_62,plain,(
    ! [E_49] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_49),'#skF_2')
      | ~ m1_subset_1(E_49,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5176,plain,(
    ! [B_393] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_393,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_393,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4667,c_62])).

tff(c_1927,plain,(
    ! [C_239,B_240] :
      ( ~ r2_hidden(k1_funct_1(C_239,'#skF_1'(k1_relat_1(C_239),B_240,C_239)),B_240)
      | v1_funct_2(C_239,k1_relat_1(C_239),B_240)
      | ~ v1_funct_1(C_239)
      | ~ v1_relat_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1930,plain,(
    ! [B_240] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_240,'#skF_5')),B_240)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_240)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_1927])).

tff(c_1932,plain,(
    ! [B_240] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_240,'#skF_5')),B_240)
      | v1_funct_2('#skF_5','#skF_3',B_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_1505,c_1930])).

tff(c_5184,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_5176,c_1932])).

tff(c_5193,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_5184])).

tff(c_5195,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5193])).

tff(c_5204,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_2707,c_5195])).

tff(c_5213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_5204])).

tff(c_5215,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5193])).

tff(c_2530,plain,(
    ! [C_274,B_275] :
      ( ~ r2_hidden(k1_funct_1(C_274,'#skF_1'(k1_relat_1(C_274),B_275,C_274)),B_275)
      | m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_274),B_275)))
      | ~ v1_funct_1(C_274)
      | ~ v1_relat_1(C_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2533,plain,(
    ! [B_275] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_275,'#skF_5')),B_275)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_275)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_2530])).

tff(c_2535,plain,(
    ! [B_275] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_275,'#skF_5')),B_275)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_275))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_68,c_1505,c_2533])).

tff(c_5180,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_5176,c_2535])).

tff(c_5190,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_5180])).

tff(c_5222,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5215,c_5190])).

tff(c_5250,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_5222,c_26])).

tff(c_5283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_5250])).

tff(c_5284,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1504])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_251,plain,(
    ! [A_90,C_91,B_92] :
      ( r1_tarski(A_90,C_91)
      | ~ r1_tarski(B_92,C_91)
      | ~ r1_tarski(A_90,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_285,plain,(
    ! [A_94,A_95] :
      ( r1_tarski(A_94,A_95)
      | ~ r1_tarski(A_94,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_251])).

tff(c_295,plain,(
    ! [B_15,A_95] :
      ( r1_tarski(k2_relat_1(B_15),A_95)
      | ~ v5_relat_1(B_15,k1_xboole_0)
      | ~ v1_relat_1(B_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_285])).

tff(c_525,plain,
    ( ~ v5_relat_1('#skF_5',k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_295,c_518])).

tff(c_531,plain,(
    ~ v5_relat_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_525])).

tff(c_5311,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5284,c_531])).

tff(c_5329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_5311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.24/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.26  
% 6.24/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.24/2.26  
% 6.24/2.26  %Foreground sorts:
% 6.24/2.26  
% 6.24/2.26  
% 6.24/2.26  %Background operators:
% 6.24/2.26  
% 6.24/2.26  
% 6.24/2.26  %Foreground operators:
% 6.24/2.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.24/2.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.24/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.24/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.24/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.24/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.24/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.24/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.24/2.26  tff('#skF_5', type, '#skF_5': $i).
% 6.24/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.24/2.26  tff('#skF_2', type, '#skF_2': $i).
% 6.24/2.26  tff('#skF_3', type, '#skF_3': $i).
% 6.24/2.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.24/2.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.24/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.24/2.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.24/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.24/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.24/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.24/2.26  tff('#skF_4', type, '#skF_4': $i).
% 6.24/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.24/2.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.24/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.24/2.26  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 6.24/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.24/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.24/2.26  
% 6.24/2.28  tff(f_146, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 6.24/2.28  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.24/2.28  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.24/2.28  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.24/2.28  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.24/2.28  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.24/2.28  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.24/2.28  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.24/2.28  tff(f_124, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 6.24/2.28  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.24/2.28  tff(f_107, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 6.24/2.28  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.24/2.28  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.24/2.28  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.24/2.28  tff(c_152, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.24/2.28  tff(c_161, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_152])).
% 6.24/2.28  tff(c_24, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.24/2.28  tff(c_114, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.24/2.28  tff(c_120, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_114])).
% 6.24/2.28  tff(c_124, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_120])).
% 6.24/2.28  tff(c_22, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.24/2.28  tff(c_508, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.24/2.28  tff(c_517, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_508])).
% 6.24/2.28  tff(c_60, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.24/2.28  tff(c_518, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_517, c_60])).
% 6.24/2.28  tff(c_528, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_518])).
% 6.24/2.28  tff(c_534, plain, (~v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_528])).
% 6.24/2.28  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.24/2.28  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.24/2.28  tff(c_572, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.24/2.28  tff(c_581, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_572])).
% 6.24/2.28  tff(c_1493, plain, (![B_203, A_204, C_205]: (k1_xboole_0=B_203 | k1_relset_1(A_204, B_203, C_205)=A_204 | ~v1_funct_2(C_205, A_204, B_203) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.24/2.28  tff(c_1500, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_1493])).
% 6.24/2.28  tff(c_1504, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_581, c_1500])).
% 6.24/2.28  tff(c_1505, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1504])).
% 6.24/2.28  tff(c_2210, plain, (![C_252, B_253]: (r2_hidden('#skF_1'(k1_relat_1(C_252), B_253, C_252), k1_relat_1(C_252)) | m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_252), B_253))) | ~v1_funct_1(C_252) | ~v1_relat_1(C_252))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.24/2.28  tff(c_2219, plain, (![B_253]: (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_253, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_253))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1505, c_2210])).
% 6.24/2.28  tff(c_2658, plain, (![B_291]: (r2_hidden('#skF_1'('#skF_3', B_291, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_291))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_68, c_1505, c_1505, c_2219])).
% 6.24/2.28  tff(c_26, plain, (![C_20, B_19, A_18]: (v5_relat_1(C_20, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.24/2.28  tff(c_2703, plain, (![B_292]: (v5_relat_1('#skF_5', B_292) | r2_hidden('#skF_1'('#skF_3', B_292, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_2658, c_26])).
% 6.24/2.28  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.24/2.28  tff(c_2707, plain, (![B_292]: (m1_subset_1('#skF_1'('#skF_3', B_292, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_292))), inference(resolution, [status(thm)], [c_2703, c_12])).
% 6.24/2.28  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.24/2.28  tff(c_2708, plain, (![B_293]: (m1_subset_1('#skF_1'('#skF_3', B_293, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_293))), inference(resolution, [status(thm)], [c_2703, c_12])).
% 6.24/2.28  tff(c_46, plain, (![A_30, B_31, C_32, D_33]: (k3_funct_2(A_30, B_31, C_32, D_33)=k1_funct_1(C_32, D_33) | ~m1_subset_1(D_33, A_30) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.24/2.28  tff(c_2710, plain, (![B_31, C_32, B_293]: (k3_funct_2('#skF_3', B_31, C_32, '#skF_1'('#skF_3', B_293, '#skF_5'))=k1_funct_1(C_32, '#skF_1'('#skF_3', B_293, '#skF_5')) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_31))) | ~v1_funct_2(C_32, '#skF_3', B_31) | ~v1_funct_1(C_32) | v1_xboole_0('#skF_3') | v5_relat_1('#skF_5', B_293))), inference(resolution, [status(thm)], [c_2708, c_46])).
% 6.24/2.28  tff(c_2714, plain, (![B_294, C_295, B_296]: (k3_funct_2('#skF_3', B_294, C_295, '#skF_1'('#skF_3', B_296, '#skF_5'))=k1_funct_1(C_295, '#skF_1'('#skF_3', B_296, '#skF_5')) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_294))) | ~v1_funct_2(C_295, '#skF_3', B_294) | ~v1_funct_1(C_295) | v5_relat_1('#skF_5', B_296))), inference(negUnitSimplification, [status(thm)], [c_72, c_2710])).
% 6.24/2.28  tff(c_2721, plain, (![B_296]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_296, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_296, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v5_relat_1('#skF_5', B_296))), inference(resolution, [status(thm)], [c_64, c_2714])).
% 6.24/2.28  tff(c_4667, plain, (![B_376]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_376, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_376, '#skF_5')) | v5_relat_1('#skF_5', B_376))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2721])).
% 6.24/2.28  tff(c_62, plain, (![E_49]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_49), '#skF_2') | ~m1_subset_1(E_49, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.24/2.28  tff(c_5176, plain, (![B_393]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_393, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_393, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_393))), inference(superposition, [status(thm), theory('equality')], [c_4667, c_62])).
% 6.24/2.28  tff(c_1927, plain, (![C_239, B_240]: (~r2_hidden(k1_funct_1(C_239, '#skF_1'(k1_relat_1(C_239), B_240, C_239)), B_240) | v1_funct_2(C_239, k1_relat_1(C_239), B_240) | ~v1_funct_1(C_239) | ~v1_relat_1(C_239))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.24/2.28  tff(c_1930, plain, (![B_240]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_240, '#skF_5')), B_240) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_240) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1505, c_1927])).
% 6.24/2.28  tff(c_1932, plain, (![B_240]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_240, '#skF_5')), B_240) | v1_funct_2('#skF_5', '#skF_3', B_240))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_68, c_1505, c_1930])).
% 6.24/2.28  tff(c_5184, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_5176, c_1932])).
% 6.24/2.28  tff(c_5193, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_534, c_5184])).
% 6.24/2.28  tff(c_5195, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5193])).
% 6.24/2.28  tff(c_5204, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_2707, c_5195])).
% 6.24/2.28  tff(c_5213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_534, c_5204])).
% 6.24/2.28  tff(c_5215, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_5193])).
% 6.24/2.28  tff(c_2530, plain, (![C_274, B_275]: (~r2_hidden(k1_funct_1(C_274, '#skF_1'(k1_relat_1(C_274), B_275, C_274)), B_275) | m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_274), B_275))) | ~v1_funct_1(C_274) | ~v1_relat_1(C_274))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.24/2.28  tff(c_2533, plain, (![B_275]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_275, '#skF_5')), B_275) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_275))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1505, c_2530])).
% 6.24/2.28  tff(c_2535, plain, (![B_275]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_275, '#skF_5')), B_275) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_275))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_68, c_1505, c_2533])).
% 6.24/2.28  tff(c_5180, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_5176, c_2535])).
% 6.24/2.28  tff(c_5190, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_534, c_5180])).
% 6.24/2.28  tff(c_5222, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5215, c_5190])).
% 6.24/2.28  tff(c_5250, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_5222, c_26])).
% 6.24/2.28  tff(c_5283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_534, c_5250])).
% 6.24/2.28  tff(c_5284, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1504])).
% 6.24/2.28  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.24/2.28  tff(c_251, plain, (![A_90, C_91, B_92]: (r1_tarski(A_90, C_91) | ~r1_tarski(B_92, C_91) | ~r1_tarski(A_90, B_92))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.24/2.28  tff(c_285, plain, (![A_94, A_95]: (r1_tarski(A_94, A_95) | ~r1_tarski(A_94, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_251])).
% 6.24/2.28  tff(c_295, plain, (![B_15, A_95]: (r1_tarski(k2_relat_1(B_15), A_95) | ~v5_relat_1(B_15, k1_xboole_0) | ~v1_relat_1(B_15))), inference(resolution, [status(thm)], [c_22, c_285])).
% 6.24/2.28  tff(c_525, plain, (~v5_relat_1('#skF_5', k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_295, c_518])).
% 6.24/2.28  tff(c_531, plain, (~v5_relat_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_525])).
% 6.24/2.28  tff(c_5311, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5284, c_531])).
% 6.24/2.28  tff(c_5329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_5311])).
% 6.24/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.28  
% 6.24/2.28  Inference rules
% 6.24/2.28  ----------------------
% 6.24/2.28  #Ref     : 0
% 6.24/2.28  #Sup     : 1067
% 6.24/2.28  #Fact    : 0
% 6.24/2.28  #Define  : 0
% 6.24/2.28  #Split   : 12
% 6.24/2.28  #Chain   : 0
% 6.24/2.28  #Close   : 0
% 6.24/2.28  
% 6.24/2.28  Ordering : KBO
% 6.24/2.28  
% 6.24/2.28  Simplification rules
% 6.24/2.28  ----------------------
% 6.24/2.28  #Subsume      : 284
% 6.24/2.28  #Demod        : 1064
% 6.24/2.28  #Tautology    : 365
% 6.24/2.28  #SimpNegUnit  : 25
% 6.24/2.28  #BackRed      : 45
% 6.24/2.28  
% 6.24/2.28  #Partial instantiations: 0
% 6.24/2.28  #Strategies tried      : 1
% 6.24/2.28  
% 6.24/2.28  Timing (in seconds)
% 6.24/2.28  ----------------------
% 6.24/2.28  Preprocessing        : 0.34
% 6.24/2.28  Parsing              : 0.17
% 6.24/2.28  CNF conversion       : 0.02
% 6.24/2.28  Main loop            : 1.11
% 6.24/2.28  Inferencing          : 0.36
% 6.24/2.28  Reduction            : 0.40
% 6.24/2.28  Demodulation         : 0.27
% 6.24/2.28  BG Simplification    : 0.04
% 6.24/2.28  Subsumption          : 0.23
% 6.24/2.28  Abstraction          : 0.06
% 6.24/2.28  MUC search           : 0.00
% 6.24/2.28  Cooper               : 0.00
% 6.24/2.28  Total                : 1.48
% 6.24/2.28  Index Insertion      : 0.00
% 6.24/2.28  Index Deletion       : 0.00
% 6.24/2.28  Index Matching       : 0.00
% 6.24/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
