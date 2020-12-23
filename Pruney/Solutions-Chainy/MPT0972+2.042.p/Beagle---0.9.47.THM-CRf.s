%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:40 EST 2020

% Result     : Theorem 4.98s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  150 (1746 expanded)
%              Number of leaves         :   46 ( 605 expanded)
%              Depth                    :   18
%              Number of atoms          :  244 (4104 expanded)
%              Number of equality atoms :   79 (1168 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
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

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_139,axiom,(
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

tff(f_100,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1785,plain,(
    ! [A_248,B_249,C_250,D_251] :
      ( r2_relset_1(A_248,B_249,C_250,C_250)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1812,plain,(
    ! [C_253] :
      ( r2_relset_1('#skF_7','#skF_8',C_253,C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_1785])).

tff(c_1820,plain,(
    r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_1812])).

tff(c_42,plain,(
    ! [A_42,B_43] : v1_relat_1(k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_74,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_129,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_74,c_129])).

tff(c_144,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_135])).

tff(c_78,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_76,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_484,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_502,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_74,c_484])).

tff(c_1848,plain,(
    ! [B_261,A_262,C_263] :
      ( k1_xboole_0 = B_261
      | k1_relset_1(A_262,B_261,C_263) = A_262
      | ~ v1_funct_2(C_263,A_262,B_261)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1854,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_1848])).

tff(c_1870,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_502,c_1854])).

tff(c_1932,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1870])).

tff(c_132,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_129])).

tff(c_141,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_132])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_82,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_501,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_484])).

tff(c_1851,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_1848])).

tff(c_1867,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_501,c_1851])).

tff(c_1874,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1867])).

tff(c_2114,plain,(
    ! [A_272,B_273] :
      ( r2_hidden('#skF_6'(A_272,B_273),k1_relat_1(A_272))
      | B_273 = A_272
      | k1_relat_1(B_273) != k1_relat_1(A_272)
      | ~ v1_funct_1(B_273)
      | ~ v1_relat_1(B_273)
      | ~ v1_funct_1(A_272)
      | ~ v1_relat_1(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2131,plain,(
    ! [B_273] :
      ( r2_hidden('#skF_6'('#skF_9',B_273),'#skF_7')
      | B_273 = '#skF_9'
      | k1_relat_1(B_273) != k1_relat_1('#skF_9')
      | ~ v1_funct_1(B_273)
      | ~ v1_relat_1(B_273)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_2114])).

tff(c_2320,plain,(
    ! [B_290] :
      ( r2_hidden('#skF_6'('#skF_9',B_290),'#skF_7')
      | B_290 = '#skF_9'
      | k1_relat_1(B_290) != '#skF_7'
      | ~ v1_funct_1(B_290)
      | ~ v1_relat_1(B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_84,c_1874,c_2131])).

tff(c_72,plain,(
    ! [E_69] :
      ( k1_funct_1('#skF_10',E_69) = k1_funct_1('#skF_9',E_69)
      | ~ r2_hidden(E_69,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2632,plain,(
    ! [B_298] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_9',B_298)) = k1_funct_1('#skF_9','#skF_6'('#skF_9',B_298))
      | B_298 = '#skF_9'
      | k1_relat_1(B_298) != '#skF_7'
      | ~ v1_funct_1(B_298)
      | ~ v1_relat_1(B_298) ) ),
    inference(resolution,[status(thm)],[c_2320,c_72])).

tff(c_44,plain,(
    ! [B_48,A_44] :
      ( k1_funct_1(B_48,'#skF_6'(A_44,B_48)) != k1_funct_1(A_44,'#skF_6'(A_44,B_48))
      | B_48 = A_44
      | k1_relat_1(B_48) != k1_relat_1(A_44)
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2639,plain,
    ( k1_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | '#skF_10' = '#skF_9'
    | k1_relat_1('#skF_10') != '#skF_7'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_2632,c_44])).

tff(c_2646,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_78,c_1932,c_141,c_84,c_1932,c_1874,c_2639])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2674,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2646,c_70])).

tff(c_2687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_2674])).

tff(c_2688,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1870])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    ! [A_74,B_75] : v1_relat_1(k2_zfmisc_1(A_74,B_75)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_114])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_190,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_209,plain,(
    ! [A_96] : v4_relat_1(k1_xboole_0,A_96) ),
    inference(resolution,[status(thm)],[c_20,c_190])).

tff(c_267,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(k1_relat_1(B_112),A_113)
      | ~ v4_relat_1(B_112,A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_282,plain,(
    ! [B_114] :
      ( k1_relat_1(B_114) = k1_xboole_0
      | ~ v4_relat_1(B_114,k1_xboole_0)
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_267,c_10])).

tff(c_286,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_209,c_282])).

tff(c_289,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_286])).

tff(c_848,plain,(
    ! [A_196,B_197] :
      ( r2_hidden(k4_tarski('#skF_2'(A_196,B_197),'#skF_3'(A_196,B_197)),A_196)
      | r2_hidden('#skF_4'(A_196,B_197),B_197)
      | k1_relat_1(A_196) = B_197 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_534,plain,(
    ! [C_156,A_157] :
      ( r2_hidden(k4_tarski(C_156,'#skF_5'(A_157,k1_relat_1(A_157),C_156)),A_157)
      | ~ r2_hidden(C_156,k1_relat_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_554,plain,(
    ! [C_156] :
      ( r2_hidden(k4_tarski(C_156,'#skF_5'(k1_xboole_0,k1_xboole_0,C_156)),k1_xboole_0)
      | ~ r2_hidden(C_156,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_534])).

tff(c_610,plain,(
    ! [C_162] :
      ( r2_hidden(k4_tarski(C_162,'#skF_5'(k1_xboole_0,k1_xboole_0,C_162)),k1_xboole_0)
      | ~ r2_hidden(C_162,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_554])).

tff(c_48,plain,(
    ! [B_51,A_50] :
      ( ~ r1_tarski(B_51,A_50)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_622,plain,(
    ! [C_162] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_162,'#skF_5'(k1_xboole_0,k1_xboole_0,C_162)))
      | ~ r2_hidden(C_162,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_610,c_48])).

tff(c_634,plain,(
    ! [C_162] : ~ r2_hidden(C_162,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_622])).

tff(c_856,plain,(
    ! [B_197] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_197),B_197)
      | k1_relat_1(k1_xboole_0) = B_197 ) ),
    inference(resolution,[status(thm)],[c_848,c_634])).

tff(c_879,plain,(
    ! [B_198] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_198),B_198)
      | k1_xboole_0 = B_198 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_856])).

tff(c_904,plain,
    ( k1_funct_1('#skF_10','#skF_4'(k1_xboole_0,'#skF_7')) = k1_funct_1('#skF_9','#skF_4'(k1_xboole_0,'#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_879,c_72])).

tff(c_1152,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_904])).

tff(c_16,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1187,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_7',B_9) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1152,c_1152,c_16])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_313,plain,(
    ! [C_118,A_119,B_120] :
      ( r2_hidden(C_118,A_119)
      | ~ r2_hidden(C_118,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_683,plain,(
    ! [A_168,B_169,A_170] :
      ( r2_hidden('#skF_1'(A_168,B_169),A_170)
      | ~ m1_subset_1(A_168,k1_zfmisc_1(A_170))
      | r1_tarski(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_6,c_313])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_709,plain,(
    ! [A_171,A_172] :
      ( ~ m1_subset_1(A_171,k1_zfmisc_1(A_172))
      | r1_tarski(A_171,A_172) ) ),
    inference(resolution,[status(thm)],[c_683,c_4])).

tff(c_719,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_709])).

tff(c_1306,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_719])).

tff(c_1459,plain,(
    ! [A_230] :
      ( A_230 = '#skF_7'
      | ~ r1_tarski(A_230,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1152,c_1152,c_10])).

tff(c_1478,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1306,c_1459])).

tff(c_720,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_74,c_709])).

tff(c_1305,plain,(
    r1_tarski('#skF_10','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_720])).

tff(c_1479,plain,(
    '#skF_7' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1305,c_1459])).

tff(c_1524,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_1479])).

tff(c_1515,plain,(
    ~ r2_relset_1('#skF_9','#skF_8','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_70])).

tff(c_1771,plain,(
    ~ r2_relset_1('#skF_9','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1524,c_1515])).

tff(c_1255,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( r2_relset_1(A_216,B_217,C_218,C_218)
      | ~ m1_subset_1(D_219,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1295,plain,(
    ! [C_222] :
      ( r2_relset_1('#skF_7','#skF_8',C_222,C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_74,c_1255])).

tff(c_1300,plain,(
    r2_relset_1('#skF_7','#skF_8','#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_1295])).

tff(c_1494,plain,(
    r2_relset_1('#skF_9','#skF_8','#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1478,c_1300])).

tff(c_1782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1771,c_1494])).

tff(c_1784,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_904])).

tff(c_2695,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_1784])).

tff(c_2718,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2688,c_289])).

tff(c_2728,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2688,c_14])).

tff(c_2835,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2728,c_719])).

tff(c_3000,plain,(
    ! [A_314] :
      ( A_314 = '#skF_8'
      | ~ r1_tarski(A_314,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2688,c_10])).

tff(c_3019,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2835,c_3000])).

tff(c_3029,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3019,c_1874])).

tff(c_3044,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2718,c_3029])).

tff(c_3046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2695,c_3044])).

tff(c_3047,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1867])).

tff(c_3276,plain,(
    ! [A_327] : m1_subset_1('#skF_8',k1_zfmisc_1(A_327)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_20])).

tff(c_1800,plain,(
    ! [A_248,B_249,C_250] :
      ( r2_relset_1(A_248,B_249,C_250,C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(resolution,[status(thm)],[c_20,c_1785])).

tff(c_3307,plain,(
    ! [A_248,B_249] : r2_relset_1(A_248,B_249,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_3276,c_1800])).

tff(c_3087,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_3047,c_14])).

tff(c_3224,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3087,c_720])).

tff(c_3363,plain,(
    ! [A_330] :
      ( A_330 = '#skF_8'
      | ~ r1_tarski(A_330,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3047,c_3047,c_10])).

tff(c_3383,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3224,c_3363])).

tff(c_3225,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3087,c_719])).

tff(c_3382,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3225,c_3363])).

tff(c_3410,plain,(
    ~ r2_relset_1('#skF_7','#skF_8','#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3382,c_70])).

tff(c_3458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3307,c_3383,c_3410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:57:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.98/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/2.00  
% 4.98/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/2.00  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.98/2.00  
% 4.98/2.00  %Foreground sorts:
% 4.98/2.00  
% 4.98/2.00  
% 4.98/2.00  %Background operators:
% 4.98/2.00  
% 4.98/2.00  
% 4.98/2.00  %Foreground operators:
% 4.98/2.00  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.98/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.98/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.98/2.00  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.98/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.98/2.00  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.98/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.98/2.00  tff('#skF_7', type, '#skF_7': $i).
% 4.98/2.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.98/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.98/2.00  tff('#skF_10', type, '#skF_10': $i).
% 4.98/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.98/2.00  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.98/2.00  tff('#skF_9', type, '#skF_9': $i).
% 4.98/2.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.98/2.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.98/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.98/2.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.98/2.00  tff('#skF_8', type, '#skF_8': $i).
% 4.98/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.98/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.98/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.98/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.98/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.98/2.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.98/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.98/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.98/2.00  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.98/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.98/2.00  
% 5.35/2.02  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 5.35/2.02  tff(f_121, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.35/2.02  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.35/2.02  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.35/2.02  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.35/2.02  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.35/2.02  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.35/2.02  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.35/2.02  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.35/2.02  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.35/2.02  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.35/2.02  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.35/2.02  tff(f_80, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.35/2.02  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.35/2.02  tff(f_105, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.35/2.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.35/2.02  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.35/2.02  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.35/2.02  tff(c_1785, plain, (![A_248, B_249, C_250, D_251]: (r2_relset_1(A_248, B_249, C_250, C_250) | ~m1_subset_1(D_251, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.35/2.02  tff(c_1812, plain, (![C_253]: (r2_relset_1('#skF_7', '#skF_8', C_253, C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))))), inference(resolution, [status(thm)], [c_80, c_1785])).
% 5.35/2.02  tff(c_1820, plain, (r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_80, c_1812])).
% 5.35/2.02  tff(c_42, plain, (![A_42, B_43]: (v1_relat_1(k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.35/2.02  tff(c_74, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.35/2.02  tff(c_129, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.35/2.02  tff(c_135, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_74, c_129])).
% 5.35/2.02  tff(c_144, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_135])).
% 5.35/2.02  tff(c_78, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.35/2.02  tff(c_76, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.35/2.02  tff(c_484, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.35/2.02  tff(c_502, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_74, c_484])).
% 5.35/2.02  tff(c_1848, plain, (![B_261, A_262, C_263]: (k1_xboole_0=B_261 | k1_relset_1(A_262, B_261, C_263)=A_262 | ~v1_funct_2(C_263, A_262, B_261) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_262, B_261))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.35/2.02  tff(c_1854, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_1848])).
% 5.35/2.02  tff(c_1870, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_502, c_1854])).
% 5.35/2.02  tff(c_1932, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_1870])).
% 5.35/2.02  tff(c_132, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_80, c_129])).
% 5.35/2.02  tff(c_141, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_132])).
% 5.35/2.02  tff(c_84, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.35/2.02  tff(c_82, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.35/2.02  tff(c_501, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_484])).
% 5.35/2.02  tff(c_1851, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_80, c_1848])).
% 5.35/2.02  tff(c_1867, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_501, c_1851])).
% 5.35/2.02  tff(c_1874, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_1867])).
% 5.35/2.02  tff(c_2114, plain, (![A_272, B_273]: (r2_hidden('#skF_6'(A_272, B_273), k1_relat_1(A_272)) | B_273=A_272 | k1_relat_1(B_273)!=k1_relat_1(A_272) | ~v1_funct_1(B_273) | ~v1_relat_1(B_273) | ~v1_funct_1(A_272) | ~v1_relat_1(A_272))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.35/2.02  tff(c_2131, plain, (![B_273]: (r2_hidden('#skF_6'('#skF_9', B_273), '#skF_7') | B_273='#skF_9' | k1_relat_1(B_273)!=k1_relat_1('#skF_9') | ~v1_funct_1(B_273) | ~v1_relat_1(B_273) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1874, c_2114])).
% 5.35/2.02  tff(c_2320, plain, (![B_290]: (r2_hidden('#skF_6'('#skF_9', B_290), '#skF_7') | B_290='#skF_9' | k1_relat_1(B_290)!='#skF_7' | ~v1_funct_1(B_290) | ~v1_relat_1(B_290))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_84, c_1874, c_2131])).
% 5.35/2.02  tff(c_72, plain, (![E_69]: (k1_funct_1('#skF_10', E_69)=k1_funct_1('#skF_9', E_69) | ~r2_hidden(E_69, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.35/2.02  tff(c_2632, plain, (![B_298]: (k1_funct_1('#skF_10', '#skF_6'('#skF_9', B_298))=k1_funct_1('#skF_9', '#skF_6'('#skF_9', B_298)) | B_298='#skF_9' | k1_relat_1(B_298)!='#skF_7' | ~v1_funct_1(B_298) | ~v1_relat_1(B_298))), inference(resolution, [status(thm)], [c_2320, c_72])).
% 5.35/2.02  tff(c_44, plain, (![B_48, A_44]: (k1_funct_1(B_48, '#skF_6'(A_44, B_48))!=k1_funct_1(A_44, '#skF_6'(A_44, B_48)) | B_48=A_44 | k1_relat_1(B_48)!=k1_relat_1(A_44) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.35/2.02  tff(c_2639, plain, (k1_relat_1('#skF_10')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | '#skF_10'='#skF_9' | k1_relat_1('#skF_10')!='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_2632, c_44])).
% 5.35/2.02  tff(c_2646, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_78, c_1932, c_141, c_84, c_1932, c_1874, c_2639])).
% 5.35/2.02  tff(c_70, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.35/2.02  tff(c_2674, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2646, c_70])).
% 5.35/2.02  tff(c_2687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1820, c_2674])).
% 5.35/2.02  tff(c_2688, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1870])).
% 5.35/2.02  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.35/2.02  tff(c_114, plain, (![A_74, B_75]: (v1_relat_1(k2_zfmisc_1(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.35/2.02  tff(c_116, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_114])).
% 5.35/2.02  tff(c_20, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.35/2.02  tff(c_190, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.35/2.02  tff(c_209, plain, (![A_96]: (v4_relat_1(k1_xboole_0, A_96))), inference(resolution, [status(thm)], [c_20, c_190])).
% 5.35/2.02  tff(c_267, plain, (![B_112, A_113]: (r1_tarski(k1_relat_1(B_112), A_113) | ~v4_relat_1(B_112, A_113) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.35/2.02  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.35/2.02  tff(c_282, plain, (![B_114]: (k1_relat_1(B_114)=k1_xboole_0 | ~v4_relat_1(B_114, k1_xboole_0) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_267, c_10])).
% 5.35/2.02  tff(c_286, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_209, c_282])).
% 5.35/2.02  tff(c_289, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_286])).
% 5.35/2.02  tff(c_848, plain, (![A_196, B_197]: (r2_hidden(k4_tarski('#skF_2'(A_196, B_197), '#skF_3'(A_196, B_197)), A_196) | r2_hidden('#skF_4'(A_196, B_197), B_197) | k1_relat_1(A_196)=B_197)), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.35/2.02  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.35/2.02  tff(c_534, plain, (![C_156, A_157]: (r2_hidden(k4_tarski(C_156, '#skF_5'(A_157, k1_relat_1(A_157), C_156)), A_157) | ~r2_hidden(C_156, k1_relat_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.35/2.02  tff(c_554, plain, (![C_156]: (r2_hidden(k4_tarski(C_156, '#skF_5'(k1_xboole_0, k1_xboole_0, C_156)), k1_xboole_0) | ~r2_hidden(C_156, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_289, c_534])).
% 5.35/2.02  tff(c_610, plain, (![C_162]: (r2_hidden(k4_tarski(C_162, '#skF_5'(k1_xboole_0, k1_xboole_0, C_162)), k1_xboole_0) | ~r2_hidden(C_162, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_554])).
% 5.35/2.02  tff(c_48, plain, (![B_51, A_50]: (~r1_tarski(B_51, A_50) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.35/2.02  tff(c_622, plain, (![C_162]: (~r1_tarski(k1_xboole_0, k4_tarski(C_162, '#skF_5'(k1_xboole_0, k1_xboole_0, C_162))) | ~r2_hidden(C_162, k1_xboole_0))), inference(resolution, [status(thm)], [c_610, c_48])).
% 5.35/2.02  tff(c_634, plain, (![C_162]: (~r2_hidden(C_162, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_622])).
% 5.35/2.02  tff(c_856, plain, (![B_197]: (r2_hidden('#skF_4'(k1_xboole_0, B_197), B_197) | k1_relat_1(k1_xboole_0)=B_197)), inference(resolution, [status(thm)], [c_848, c_634])).
% 5.35/2.02  tff(c_879, plain, (![B_198]: (r2_hidden('#skF_4'(k1_xboole_0, B_198), B_198) | k1_xboole_0=B_198)), inference(demodulation, [status(thm), theory('equality')], [c_289, c_856])).
% 5.35/2.02  tff(c_904, plain, (k1_funct_1('#skF_10', '#skF_4'(k1_xboole_0, '#skF_7'))=k1_funct_1('#skF_9', '#skF_4'(k1_xboole_0, '#skF_7')) | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_879, c_72])).
% 5.35/2.02  tff(c_1152, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_904])).
% 5.35/2.02  tff(c_16, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.35/2.02  tff(c_1187, plain, (![B_9]: (k2_zfmisc_1('#skF_7', B_9)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1152, c_1152, c_16])).
% 5.35/2.02  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.02  tff(c_313, plain, (![C_118, A_119, B_120]: (r2_hidden(C_118, A_119) | ~r2_hidden(C_118, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.35/2.02  tff(c_683, plain, (![A_168, B_169, A_170]: (r2_hidden('#skF_1'(A_168, B_169), A_170) | ~m1_subset_1(A_168, k1_zfmisc_1(A_170)) | r1_tarski(A_168, B_169))), inference(resolution, [status(thm)], [c_6, c_313])).
% 5.35/2.02  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.02  tff(c_709, plain, (![A_171, A_172]: (~m1_subset_1(A_171, k1_zfmisc_1(A_172)) | r1_tarski(A_171, A_172))), inference(resolution, [status(thm)], [c_683, c_4])).
% 5.35/2.02  tff(c_719, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_80, c_709])).
% 5.35/2.02  tff(c_1306, plain, (r1_tarski('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_719])).
% 5.35/2.02  tff(c_1459, plain, (![A_230]: (A_230='#skF_7' | ~r1_tarski(A_230, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1152, c_1152, c_10])).
% 5.35/2.02  tff(c_1478, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_1306, c_1459])).
% 5.35/2.02  tff(c_720, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_74, c_709])).
% 5.35/2.02  tff(c_1305, plain, (r1_tarski('#skF_10', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_720])).
% 5.35/2.02  tff(c_1479, plain, ('#skF_7'='#skF_10'), inference(resolution, [status(thm)], [c_1305, c_1459])).
% 5.35/2.02  tff(c_1524, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_1479])).
% 5.35/2.02  tff(c_1515, plain, (~r2_relset_1('#skF_9', '#skF_8', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_70])).
% 5.35/2.02  tff(c_1771, plain, (~r2_relset_1('#skF_9', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1524, c_1515])).
% 5.35/2.02  tff(c_1255, plain, (![A_216, B_217, C_218, D_219]: (r2_relset_1(A_216, B_217, C_218, C_218) | ~m1_subset_1(D_219, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.35/2.02  tff(c_1295, plain, (![C_222]: (r2_relset_1('#skF_7', '#skF_8', C_222, C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))))), inference(resolution, [status(thm)], [c_74, c_1255])).
% 5.35/2.02  tff(c_1300, plain, (r2_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_80, c_1295])).
% 5.35/2.02  tff(c_1494, plain, (r2_relset_1('#skF_9', '#skF_8', '#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1478, c_1300])).
% 5.35/2.02  tff(c_1782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1771, c_1494])).
% 5.35/2.02  tff(c_1784, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_904])).
% 5.35/2.02  tff(c_2695, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_1784])).
% 5.35/2.02  tff(c_2718, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2688, c_289])).
% 5.35/2.02  tff(c_2728, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2688, c_14])).
% 5.35/2.02  tff(c_2835, plain, (r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2728, c_719])).
% 5.35/2.02  tff(c_3000, plain, (![A_314]: (A_314='#skF_8' | ~r1_tarski(A_314, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2688, c_10])).
% 5.35/2.02  tff(c_3019, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_2835, c_3000])).
% 5.35/2.02  tff(c_3029, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3019, c_1874])).
% 5.35/2.02  tff(c_3044, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2718, c_3029])).
% 5.35/2.02  tff(c_3046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2695, c_3044])).
% 5.35/2.02  tff(c_3047, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1867])).
% 5.35/2.02  tff(c_3276, plain, (![A_327]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_327)))), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_20])).
% 5.35/2.02  tff(c_1800, plain, (![A_248, B_249, C_250]: (r2_relset_1(A_248, B_249, C_250, C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(resolution, [status(thm)], [c_20, c_1785])).
% 5.35/2.02  tff(c_3307, plain, (![A_248, B_249]: (r2_relset_1(A_248, B_249, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_3276, c_1800])).
% 5.35/2.02  tff(c_3087, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_3047, c_14])).
% 5.35/2.02  tff(c_3224, plain, (r1_tarski('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3087, c_720])).
% 5.35/2.02  tff(c_3363, plain, (![A_330]: (A_330='#skF_8' | ~r1_tarski(A_330, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3047, c_3047, c_10])).
% 5.35/2.02  tff(c_3383, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_3224, c_3363])).
% 5.35/2.02  tff(c_3225, plain, (r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3087, c_719])).
% 5.35/2.02  tff(c_3382, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_3225, c_3363])).
% 5.35/2.02  tff(c_3410, plain, (~r2_relset_1('#skF_7', '#skF_8', '#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3382, c_70])).
% 5.35/2.02  tff(c_3458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3307, c_3383, c_3410])).
% 5.35/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.02  
% 5.35/2.02  Inference rules
% 5.35/2.02  ----------------------
% 5.35/2.02  #Ref     : 4
% 5.35/2.02  #Sup     : 665
% 5.35/2.02  #Fact    : 0
% 5.35/2.02  #Define  : 0
% 5.35/2.02  #Split   : 6
% 5.35/2.02  #Chain   : 0
% 5.35/2.02  #Close   : 0
% 5.35/2.02  
% 5.35/2.02  Ordering : KBO
% 5.35/2.02  
% 5.35/2.02  Simplification rules
% 5.35/2.02  ----------------------
% 5.35/2.02  #Subsume      : 133
% 5.35/2.02  #Demod        : 813
% 5.35/2.02  #Tautology    : 328
% 5.35/2.02  #SimpNegUnit  : 19
% 5.35/2.02  #BackRed      : 236
% 5.35/2.02  
% 5.35/2.02  #Partial instantiations: 0
% 5.35/2.02  #Strategies tried      : 1
% 5.35/2.02  
% 5.35/2.02  Timing (in seconds)
% 5.35/2.02  ----------------------
% 5.35/2.02  Preprocessing        : 0.38
% 5.35/2.02  Parsing              : 0.19
% 5.35/2.02  CNF conversion       : 0.03
% 5.35/2.02  Main loop            : 0.80
% 5.35/2.02  Inferencing          : 0.25
% 5.35/2.02  Reduction            : 0.29
% 5.35/2.02  Demodulation         : 0.21
% 5.35/2.02  BG Simplification    : 0.04
% 5.35/2.02  Subsumption          : 0.15
% 5.35/2.02  Abstraction          : 0.03
% 5.35/2.02  MUC search           : 0.00
% 5.35/2.02  Cooper               : 0.00
% 5.35/2.02  Total                : 1.23
% 5.35/2.02  Index Insertion      : 0.00
% 5.35/2.02  Index Deletion       : 0.00
% 5.35/2.03  Index Matching       : 0.00
% 5.35/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
