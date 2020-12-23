%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:13 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 777 expanded)
%              Number of leaves         :   46 ( 251 expanded)
%              Depth                    :   14
%              Number of atoms          :  326 (2148 expanded)
%              Number of equality atoms :   48 ( 588 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_180,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_148,axiom,(
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

tff(f_160,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_5189,plain,(
    ! [C_350,A_351,B_352] :
      ( v1_relat_1(C_350)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5202,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_5189])).

tff(c_5252,plain,(
    ! [C_367,B_368,A_369] :
      ( v5_relat_1(C_367,B_368)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_369,B_368))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5265,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_5252])).

tff(c_5469,plain,(
    ! [B_398,A_399] :
      ( r1_tarski(k2_relat_1(B_398),A_399)
      | ~ v5_relat_1(B_398,A_399)
      | ~ v1_relat_1(B_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_78,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_5269,plain,(
    ! [A_372,C_373,B_374] :
      ( r1_tarski(A_372,C_373)
      | ~ r1_tarski(B_374,C_373)
      | ~ r1_tarski(A_372,B_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5282,plain,(
    ! [A_375] :
      ( r1_tarski(A_375,'#skF_5')
      | ~ r1_tarski(A_375,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_5269])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( v5_relat_1(B_24,A_23)
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5296,plain,(
    ! [B_24] :
      ( v5_relat_1(B_24,'#skF_5')
      | ~ v1_relat_1(B_24)
      | ~ r1_tarski(k2_relat_1(B_24),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5282,c_32])).

tff(c_5509,plain,(
    ! [B_398] :
      ( v5_relat_1(B_398,'#skF_5')
      | ~ v5_relat_1(B_398,'#skF_4')
      | ~ v1_relat_1(B_398) ) ),
    inference(resolution,[status(thm)],[c_5469,c_5296])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7263,plain,(
    ! [D_522,C_523,B_524,A_525] :
      ( m1_subset_1(D_522,k1_zfmisc_1(k2_zfmisc_1(C_523,B_524)))
      | ~ r1_tarski(k2_relat_1(D_522),B_524)
      | ~ m1_subset_1(D_522,k1_zfmisc_1(k2_zfmisc_1(C_523,A_525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7297,plain,(
    ! [B_526] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_526)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_526) ) ),
    inference(resolution,[status(thm)],[c_80,c_7263])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_86,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_74])).

tff(c_127,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_174,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_161])).

tff(c_527,plain,(
    ! [C_118,B_119,A_120] :
      ( v5_relat_1(C_118,B_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_540,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_527])).

tff(c_398,plain,(
    ! [A_106,C_107,B_108] :
      ( r1_tarski(A_106,C_107)
      | ~ r1_tarski(B_108,C_107)
      | ~ r1_tarski(A_106,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_416,plain,(
    ! [A_106] :
      ( r1_tarski(A_106,'#skF_5')
      | ~ r1_tarski(A_106,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_398])).

tff(c_4139,plain,(
    ! [D_312,C_313,B_314,A_315] :
      ( m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(C_313,B_314)))
      | ~ r1_tarski(k2_relat_1(D_312),B_314)
      | ~ m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(C_313,A_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4168,plain,(
    ! [B_316] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_316)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_316) ) ),
    inference(resolution,[status(thm)],[c_80,c_4139])).

tff(c_46,plain,(
    ! [C_35,B_34,A_33] :
      ( v5_relat_1(C_35,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4209,plain,(
    ! [B_317] :
      ( v5_relat_1('#skF_6',B_317)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_317) ) ),
    inference(resolution,[status(thm)],[c_4168,c_46])).

tff(c_4234,plain,
    ( v5_relat_1('#skF_6','#skF_5')
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_416,c_4209])).

tff(c_4239,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4234])).

tff(c_4245,plain,
    ( ~ v5_relat_1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_4239])).

tff(c_4252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_540,c_4245])).

tff(c_4254,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4234])).

tff(c_417,plain,(
    ! [A_109] :
      ( r1_tarski(A_109,'#skF_5')
      | ~ r1_tarski(A_109,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_398])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_430,plain,(
    ! [A_9,A_109] :
      ( r1_tarski(A_9,'#skF_5')
      | ~ r1_tarski(A_9,A_109)
      | ~ r1_tarski(A_109,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_417,c_14])).

tff(c_4264,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_4254,c_430])).

tff(c_4280,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4264])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_944,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_960,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_944])).

tff(c_4311,plain,(
    ! [B_318,A_319,C_320] :
      ( k1_xboole_0 = B_318
      | k1_relset_1(A_319,B_318,C_320) = A_319
      | ~ v1_funct_2(C_320,A_319,B_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_319,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4338,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_4311])).

tff(c_4351,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_960,c_4338])).

tff(c_4352,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4351])).

tff(c_70,plain,(
    ! [B_51,A_50] :
      ( v1_funct_2(B_51,k1_relat_1(B_51),A_50)
      | ~ r1_tarski(k2_relat_1(B_51),A_50)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4380,plain,(
    ! [A_50] :
      ( v1_funct_2('#skF_6','#skF_3',A_50)
      | ~ r1_tarski(k2_relat_1('#skF_6'),A_50)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4352,c_70])).

tff(c_5105,plain,(
    ! [A_345] :
      ( v1_funct_2('#skF_6','#skF_3',A_345)
      | ~ r1_tarski(k2_relat_1('#skF_6'),A_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_84,c_4380])).

tff(c_5108,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_4280,c_5105])).

tff(c_5135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_5108])).

tff(c_5136,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_7340,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_7297,c_5136])).

tff(c_7354,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_7340])).

tff(c_7364,plain,(
    ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5202,c_7354])).

tff(c_7374,plain,
    ( ~ v5_relat_1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5509,c_7364])).

tff(c_7382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5202,c_5265,c_7374])).

tff(c_7384,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_20,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7402,plain,(
    ! [A_15] : m1_subset_1('#skF_4',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7384,c_20])).

tff(c_7421,plain,(
    ! [A_537,B_538] :
      ( r1_tarski(A_537,B_538)
      | ~ m1_subset_1(A_537,k1_zfmisc_1(B_538)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7433,plain,(
    ! [A_15] : r1_tarski('#skF_4',A_15) ),
    inference(resolution,[status(thm)],[c_7402,c_7421])).

tff(c_7383,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_7390,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7384,c_7383])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7385,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7383,c_16])).

tff(c_7400,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7390,c_7385])).

tff(c_7436,plain,(
    ! [B_540,A_541] :
      ( ~ r1_xboole_0(B_540,A_541)
      | ~ r1_tarski(B_540,A_541)
      | v1_xboole_0(B_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_9305,plain,(
    ! [A_734] :
      ( ~ r1_tarski(A_734,'#skF_4')
      | v1_xboole_0(A_734) ) ),
    inference(resolution,[status(thm)],[c_7400,c_7436])).

tff(c_9314,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7433,c_9305])).

tff(c_7405,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7390,c_80])).

tff(c_10122,plain,(
    ! [C_816,B_817,A_818] :
      ( v1_xboole_0(C_816)
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_zfmisc_1(B_817,A_818)))
      | ~ v1_xboole_0(A_818) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_10137,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7405,c_10122])).

tff(c_10147,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9314,c_10137])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7414,plain,(
    ! [A_533] :
      ( r2_hidden('#skF_2'(A_533),A_533)
      | A_533 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7384,c_6])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7418,plain,(
    ! [A_533] :
      ( ~ v1_xboole_0(A_533)
      | A_533 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_7414,c_2])).

tff(c_10153,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10147,c_7418])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7460,plain,(
    ! [C_543,A_544,B_545] :
      ( v1_relat_1(C_543)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7474,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7402,c_7460])).

tff(c_7413,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7384,c_6])).

tff(c_7443,plain,(
    ! [A_542] :
      ( ~ r1_tarski(A_542,'#skF_4')
      | v1_xboole_0(A_542) ) ),
    inference(resolution,[status(thm)],[c_7400,c_7436])).

tff(c_7452,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7433,c_7443])).

tff(c_7909,plain,(
    ! [C_599,B_600,A_601] :
      ( v1_xboole_0(C_599)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(B_600,A_601)))
      | ~ v1_xboole_0(A_601) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8234,plain,(
    ! [A_633,A_634,B_635] :
      ( v1_xboole_0(A_633)
      | ~ v1_xboole_0(A_634)
      | ~ r1_tarski(A_633,k2_zfmisc_1(B_635,A_634)) ) ),
    inference(resolution,[status(thm)],[c_24,c_7909])).

tff(c_8256,plain,(
    ! [B_636,A_637] :
      ( v1_xboole_0(k2_zfmisc_1(B_636,A_637))
      | ~ v1_xboole_0(A_637) ) ),
    inference(resolution,[status(thm)],[c_12,c_8234])).

tff(c_8261,plain,(
    ! [B_638,A_639] :
      ( k2_zfmisc_1(B_638,A_639) = '#skF_4'
      | ~ v1_xboole_0(A_639) ) ),
    inference(resolution,[status(thm)],[c_8256,c_7418])).

tff(c_8273,plain,(
    ! [B_638] : k2_zfmisc_1(B_638,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7452,c_8261])).

tff(c_7916,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7405,c_7909])).

tff(c_7924,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7452,c_7916])).

tff(c_7930,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7924,c_7418])).

tff(c_7432,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7405,c_7421])).

tff(c_7475,plain,(
    ! [B_546,A_547] :
      ( B_546 = A_547
      | ~ r1_tarski(B_546,A_547)
      | ~ r1_tarski(A_547,B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7482,plain,
    ( k2_zfmisc_1('#skF_4','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_7432,c_7475])).

tff(c_7501,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7482])).

tff(c_7939,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7930,c_7501])).

tff(c_8277,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8273,c_7939])).

tff(c_8282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8277])).

tff(c_8283,plain,(
    k2_zfmisc_1('#skF_4','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7482])).

tff(c_8300,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8283,c_7405])).

tff(c_8748,plain,(
    ! [A_693,C_694,B_695] :
      ( m1_subset_1(A_693,C_694)
      | ~ m1_subset_1(B_695,k1_zfmisc_1(C_694))
      | ~ r2_hidden(A_693,B_695) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8769,plain,(
    ! [A_698] :
      ( m1_subset_1(A_698,'#skF_6')
      | ~ r2_hidden(A_698,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8300,c_8748])).

tff(c_8778,plain,
    ( m1_subset_1('#skF_2'('#skF_6'),'#skF_6')
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7413,c_8769])).

tff(c_8780,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8778])).

tff(c_8799,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8780,c_84])).

tff(c_8422,plain,(
    ! [C_663,B_664,A_665] :
      ( v5_relat_1(C_663,B_664)
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(A_665,B_664))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8435,plain,(
    ! [B_664] : v5_relat_1('#skF_4',B_664) ),
    inference(resolution,[status(thm)],[c_7402,c_8422])).

tff(c_8569,plain,(
    ! [B_675,A_676] :
      ( r1_tarski(k2_relat_1(B_675),A_676)
      | ~ v5_relat_1(B_675,A_676)
      | ~ v1_relat_1(B_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7440,plain,(
    ! [A_12] :
      ( ~ r1_tarski(A_12,'#skF_4')
      | v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_7400,c_7436])).

tff(c_8743,plain,(
    ! [B_692] :
      ( v1_xboole_0(k2_relat_1(B_692))
      | ~ v5_relat_1(B_692,'#skF_4')
      | ~ v1_relat_1(B_692) ) ),
    inference(resolution,[status(thm)],[c_8569,c_7440])).

tff(c_8963,plain,(
    ! [B_714] :
      ( k2_relat_1(B_714) = '#skF_4'
      | ~ v5_relat_1(B_714,'#skF_4')
      | ~ v1_relat_1(B_714) ) ),
    inference(resolution,[status(thm)],[c_8743,c_7418])).

tff(c_8974,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8435,c_8963])).

tff(c_8981,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7474,c_8974])).

tff(c_8437,plain,(
    ! [C_667,A_668,B_669] :
      ( v4_relat_1(C_667,A_668)
      | ~ m1_subset_1(C_667,k1_zfmisc_1(k2_zfmisc_1(A_668,B_669))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8451,plain,(
    ! [A_670] : v4_relat_1('#skF_4',A_670) ),
    inference(resolution,[status(thm)],[c_7402,c_8437])).

tff(c_8285,plain,(
    ! [B_640,A_641] :
      ( r1_tarski(k1_relat_1(B_640),A_641)
      | ~ v4_relat_1(B_640,A_641)
      | ~ v1_relat_1(B_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7483,plain,(
    ! [A_15] :
      ( A_15 = '#skF_4'
      | ~ r1_tarski(A_15,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7433,c_7475])).

tff(c_8296,plain,(
    ! [B_640] :
      ( k1_relat_1(B_640) = '#skF_4'
      | ~ v4_relat_1(B_640,'#skF_4')
      | ~ v1_relat_1(B_640) ) ),
    inference(resolution,[status(thm)],[c_8285,c_7483])).

tff(c_8455,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8451,c_8296])).

tff(c_8458,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7474,c_8455])).

tff(c_9131,plain,(
    ! [B_725,A_726] :
      ( v1_funct_2(B_725,k1_relat_1(B_725),A_726)
      | ~ r1_tarski(k2_relat_1(B_725),A_726)
      | ~ v1_funct_1(B_725)
      | ~ v1_relat_1(B_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_9137,plain,(
    ! [A_726] :
      ( v1_funct_2('#skF_4','#skF_4',A_726)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_726)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8458,c_9131])).

tff(c_9141,plain,(
    ! [A_726] : v1_funct_2('#skF_4','#skF_4',A_726) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7474,c_8799,c_7433,c_8981,c_9137])).

tff(c_7441,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7390,c_7390,c_86])).

tff(c_7442,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7441])).

tff(c_8797,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8780,c_7442])).

tff(c_9145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9141,c_8797])).

tff(c_9147,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8778])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8779,plain,
    ( m1_subset_1('#skF_1'('#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_8769])).

tff(c_9148,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8779])).

tff(c_9151,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9148,c_7418])).

tff(c_9155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9147,c_9151])).

tff(c_9157,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_8779])).

tff(c_9207,plain,(
    ! [C_728,B_729,A_730] :
      ( v1_xboole_0(C_728)
      | ~ m1_subset_1(C_728,k1_zfmisc_1(k2_zfmisc_1(B_729,A_730)))
      | ~ v1_xboole_0(A_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_9210,plain,(
    ! [C_728] :
      ( v1_xboole_0(C_728)
      | ~ m1_subset_1(C_728,k1_zfmisc_1('#skF_6'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8283,c_9207])).

tff(c_9287,plain,(
    ! [C_733] :
      ( v1_xboole_0(C_733)
      | ~ m1_subset_1(C_733,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7452,c_9210])).

tff(c_9290,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_8300,c_9287])).

tff(c_9302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9157,c_9290])).

tff(c_9303,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_7441])).

tff(c_9325,plain,(
    ~ r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_9303])).

tff(c_10170,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10153,c_9325])).

tff(c_10185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7433,c_10170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:23:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.84/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.65  
% 7.84/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 7.84/2.65  
% 7.84/2.65  %Foreground sorts:
% 7.84/2.65  
% 7.84/2.65  
% 7.84/2.65  %Background operators:
% 7.84/2.65  
% 7.84/2.65  
% 7.84/2.65  %Foreground operators:
% 7.84/2.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.84/2.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.84/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.84/2.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.84/2.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.84/2.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.84/2.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.84/2.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.84/2.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.84/2.65  tff('#skF_5', type, '#skF_5': $i).
% 7.84/2.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.84/2.65  tff('#skF_6', type, '#skF_6': $i).
% 7.84/2.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.84/2.65  tff('#skF_3', type, '#skF_3': $i).
% 7.84/2.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.84/2.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.84/2.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.84/2.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.84/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.84/2.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.84/2.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.84/2.65  tff('#skF_4', type, '#skF_4': $i).
% 7.84/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.84/2.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.84/2.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.84/2.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.84/2.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.84/2.65  
% 8.01/2.67  tff(f_180, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 8.01/2.67  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.01/2.67  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.01/2.67  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.01/2.67  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.01/2.67  tff(f_130, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 8.01/2.67  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.01/2.67  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.01/2.67  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.01/2.67  tff(f_160, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 8.01/2.67  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.01/2.67  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.01/2.67  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.01/2.67  tff(f_61, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.01/2.67  tff(f_120, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.01/2.67  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.01/2.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.01/2.67  tff(f_73, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 8.01/2.67  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.01/2.67  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.01/2.67  tff(c_5189, plain, (![C_350, A_351, B_352]: (v1_relat_1(C_350) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.01/2.67  tff(c_5202, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_5189])).
% 8.01/2.67  tff(c_5252, plain, (![C_367, B_368, A_369]: (v5_relat_1(C_367, B_368) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_369, B_368))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.01/2.67  tff(c_5265, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_5252])).
% 8.01/2.67  tff(c_5469, plain, (![B_398, A_399]: (r1_tarski(k2_relat_1(B_398), A_399) | ~v5_relat_1(B_398, A_399) | ~v1_relat_1(B_398))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.01/2.67  tff(c_78, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.01/2.67  tff(c_5269, plain, (![A_372, C_373, B_374]: (r1_tarski(A_372, C_373) | ~r1_tarski(B_374, C_373) | ~r1_tarski(A_372, B_374))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.01/2.67  tff(c_5282, plain, (![A_375]: (r1_tarski(A_375, '#skF_5') | ~r1_tarski(A_375, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_5269])).
% 8.01/2.67  tff(c_32, plain, (![B_24, A_23]: (v5_relat_1(B_24, A_23) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.01/2.67  tff(c_5296, plain, (![B_24]: (v5_relat_1(B_24, '#skF_5') | ~v1_relat_1(B_24) | ~r1_tarski(k2_relat_1(B_24), '#skF_4'))), inference(resolution, [status(thm)], [c_5282, c_32])).
% 8.01/2.67  tff(c_5509, plain, (![B_398]: (v5_relat_1(B_398, '#skF_5') | ~v5_relat_1(B_398, '#skF_4') | ~v1_relat_1(B_398))), inference(resolution, [status(thm)], [c_5469, c_5296])).
% 8.01/2.67  tff(c_34, plain, (![B_24, A_23]: (r1_tarski(k2_relat_1(B_24), A_23) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.01/2.67  tff(c_7263, plain, (![D_522, C_523, B_524, A_525]: (m1_subset_1(D_522, k1_zfmisc_1(k2_zfmisc_1(C_523, B_524))) | ~r1_tarski(k2_relat_1(D_522), B_524) | ~m1_subset_1(D_522, k1_zfmisc_1(k2_zfmisc_1(C_523, A_525))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.01/2.67  tff(c_7297, plain, (![B_526]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_526))) | ~r1_tarski(k2_relat_1('#skF_6'), B_526))), inference(resolution, [status(thm)], [c_80, c_7263])).
% 8.01/2.67  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.01/2.67  tff(c_74, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.01/2.67  tff(c_86, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_74])).
% 8.01/2.67  tff(c_127, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 8.01/2.67  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.01/2.67  tff(c_161, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.01/2.67  tff(c_174, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_161])).
% 8.01/2.67  tff(c_527, plain, (![C_118, B_119, A_120]: (v5_relat_1(C_118, B_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.01/2.67  tff(c_540, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_527])).
% 8.01/2.67  tff(c_398, plain, (![A_106, C_107, B_108]: (r1_tarski(A_106, C_107) | ~r1_tarski(B_108, C_107) | ~r1_tarski(A_106, B_108))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.01/2.67  tff(c_416, plain, (![A_106]: (r1_tarski(A_106, '#skF_5') | ~r1_tarski(A_106, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_398])).
% 8.01/2.67  tff(c_4139, plain, (![D_312, C_313, B_314, A_315]: (m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(C_313, B_314))) | ~r1_tarski(k2_relat_1(D_312), B_314) | ~m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(C_313, A_315))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.01/2.67  tff(c_4168, plain, (![B_316]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_316))) | ~r1_tarski(k2_relat_1('#skF_6'), B_316))), inference(resolution, [status(thm)], [c_80, c_4139])).
% 8.01/2.67  tff(c_46, plain, (![C_35, B_34, A_33]: (v5_relat_1(C_35, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.01/2.67  tff(c_4209, plain, (![B_317]: (v5_relat_1('#skF_6', B_317) | ~r1_tarski(k2_relat_1('#skF_6'), B_317))), inference(resolution, [status(thm)], [c_4168, c_46])).
% 8.01/2.67  tff(c_4234, plain, (v5_relat_1('#skF_6', '#skF_5') | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_416, c_4209])).
% 8.01/2.67  tff(c_4239, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4234])).
% 8.01/2.67  tff(c_4245, plain, (~v5_relat_1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_4239])).
% 8.01/2.67  tff(c_4252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_540, c_4245])).
% 8.01/2.67  tff(c_4254, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_4234])).
% 8.01/2.67  tff(c_417, plain, (![A_109]: (r1_tarski(A_109, '#skF_5') | ~r1_tarski(A_109, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_398])).
% 8.01/2.67  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.01/2.67  tff(c_430, plain, (![A_9, A_109]: (r1_tarski(A_9, '#skF_5') | ~r1_tarski(A_9, A_109) | ~r1_tarski(A_109, '#skF_4'))), inference(resolution, [status(thm)], [c_417, c_14])).
% 8.01/2.67  tff(c_4264, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_4254, c_430])).
% 8.01/2.67  tff(c_4280, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4264])).
% 8.01/2.67  tff(c_76, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.01/2.67  tff(c_92, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_76])).
% 8.01/2.67  tff(c_82, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 8.01/2.67  tff(c_944, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.01/2.67  tff(c_960, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_944])).
% 8.01/2.67  tff(c_4311, plain, (![B_318, A_319, C_320]: (k1_xboole_0=B_318 | k1_relset_1(A_319, B_318, C_320)=A_319 | ~v1_funct_2(C_320, A_319, B_318) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_319, B_318))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.01/2.67  tff(c_4338, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_4311])).
% 8.01/2.67  tff(c_4351, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_960, c_4338])).
% 8.01/2.67  tff(c_4352, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_92, c_4351])).
% 8.01/2.67  tff(c_70, plain, (![B_51, A_50]: (v1_funct_2(B_51, k1_relat_1(B_51), A_50) | ~r1_tarski(k2_relat_1(B_51), A_50) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.01/2.67  tff(c_4380, plain, (![A_50]: (v1_funct_2('#skF_6', '#skF_3', A_50) | ~r1_tarski(k2_relat_1('#skF_6'), A_50) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4352, c_70])).
% 8.01/2.67  tff(c_5105, plain, (![A_345]: (v1_funct_2('#skF_6', '#skF_3', A_345) | ~r1_tarski(k2_relat_1('#skF_6'), A_345))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_84, c_4380])).
% 8.01/2.67  tff(c_5108, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_4280, c_5105])).
% 8.01/2.67  tff(c_5135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_5108])).
% 8.01/2.67  tff(c_5136, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_86])).
% 8.01/2.67  tff(c_7340, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_7297, c_5136])).
% 8.01/2.67  tff(c_7354, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_7340])).
% 8.01/2.67  tff(c_7364, plain, (~v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5202, c_7354])).
% 8.01/2.67  tff(c_7374, plain, (~v5_relat_1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5509, c_7364])).
% 8.01/2.67  tff(c_7382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5202, c_5265, c_7374])).
% 8.01/2.67  tff(c_7384, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_76])).
% 8.01/2.67  tff(c_20, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.01/2.67  tff(c_7402, plain, (![A_15]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_7384, c_20])).
% 8.01/2.67  tff(c_7421, plain, (![A_537, B_538]: (r1_tarski(A_537, B_538) | ~m1_subset_1(A_537, k1_zfmisc_1(B_538)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.01/2.67  tff(c_7433, plain, (![A_15]: (r1_tarski('#skF_4', A_15))), inference(resolution, [status(thm)], [c_7402, c_7421])).
% 8.01/2.67  tff(c_7383, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_76])).
% 8.01/2.67  tff(c_7390, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7384, c_7383])).
% 8.01/2.67  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.01/2.67  tff(c_7385, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7383, c_16])).
% 8.01/2.67  tff(c_7400, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7390, c_7385])).
% 8.01/2.67  tff(c_7436, plain, (![B_540, A_541]: (~r1_xboole_0(B_540, A_541) | ~r1_tarski(B_540, A_541) | v1_xboole_0(B_540))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.01/2.67  tff(c_9305, plain, (![A_734]: (~r1_tarski(A_734, '#skF_4') | v1_xboole_0(A_734))), inference(resolution, [status(thm)], [c_7400, c_7436])).
% 8.01/2.67  tff(c_9314, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_7433, c_9305])).
% 8.01/2.67  tff(c_7405, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7390, c_80])).
% 8.01/2.67  tff(c_10122, plain, (![C_816, B_817, A_818]: (v1_xboole_0(C_816) | ~m1_subset_1(C_816, k1_zfmisc_1(k2_zfmisc_1(B_817, A_818))) | ~v1_xboole_0(A_818))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.01/2.67  tff(c_10137, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_7405, c_10122])).
% 8.01/2.67  tff(c_10147, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9314, c_10137])).
% 8.01/2.67  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.01/2.67  tff(c_7414, plain, (![A_533]: (r2_hidden('#skF_2'(A_533), A_533) | A_533='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7384, c_6])).
% 8.01/2.67  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.67  tff(c_7418, plain, (![A_533]: (~v1_xboole_0(A_533) | A_533='#skF_4')), inference(resolution, [status(thm)], [c_7414, c_2])).
% 8.01/2.67  tff(c_10153, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_10147, c_7418])).
% 8.01/2.67  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.01/2.67  tff(c_7460, plain, (![C_543, A_544, B_545]: (v1_relat_1(C_543) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.01/2.67  tff(c_7474, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_7402, c_7460])).
% 8.01/2.67  tff(c_7413, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7384, c_6])).
% 8.01/2.67  tff(c_7443, plain, (![A_542]: (~r1_tarski(A_542, '#skF_4') | v1_xboole_0(A_542))), inference(resolution, [status(thm)], [c_7400, c_7436])).
% 8.01/2.67  tff(c_7452, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_7433, c_7443])).
% 8.01/2.67  tff(c_7909, plain, (![C_599, B_600, A_601]: (v1_xboole_0(C_599) | ~m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(B_600, A_601))) | ~v1_xboole_0(A_601))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.01/2.67  tff(c_8234, plain, (![A_633, A_634, B_635]: (v1_xboole_0(A_633) | ~v1_xboole_0(A_634) | ~r1_tarski(A_633, k2_zfmisc_1(B_635, A_634)))), inference(resolution, [status(thm)], [c_24, c_7909])).
% 8.01/2.67  tff(c_8256, plain, (![B_636, A_637]: (v1_xboole_0(k2_zfmisc_1(B_636, A_637)) | ~v1_xboole_0(A_637))), inference(resolution, [status(thm)], [c_12, c_8234])).
% 8.01/2.67  tff(c_8261, plain, (![B_638, A_639]: (k2_zfmisc_1(B_638, A_639)='#skF_4' | ~v1_xboole_0(A_639))), inference(resolution, [status(thm)], [c_8256, c_7418])).
% 8.01/2.67  tff(c_8273, plain, (![B_638]: (k2_zfmisc_1(B_638, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_7452, c_8261])).
% 8.01/2.67  tff(c_7916, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_7405, c_7909])).
% 8.01/2.67  tff(c_7924, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7452, c_7916])).
% 8.01/2.67  tff(c_7930, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_7924, c_7418])).
% 8.01/2.67  tff(c_7432, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_7405, c_7421])).
% 8.01/2.67  tff(c_7475, plain, (![B_546, A_547]: (B_546=A_547 | ~r1_tarski(B_546, A_547) | ~r1_tarski(A_547, B_546))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.01/2.67  tff(c_7482, plain, (k2_zfmisc_1('#skF_4', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_7432, c_7475])).
% 8.01/2.67  tff(c_7501, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_7482])).
% 8.01/2.67  tff(c_7939, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7930, c_7501])).
% 8.01/2.67  tff(c_8277, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8273, c_7939])).
% 8.01/2.67  tff(c_8282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8277])).
% 8.01/2.67  tff(c_8283, plain, (k2_zfmisc_1('#skF_4', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_7482])).
% 8.01/2.67  tff(c_8300, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8283, c_7405])).
% 8.01/2.67  tff(c_8748, plain, (![A_693, C_694, B_695]: (m1_subset_1(A_693, C_694) | ~m1_subset_1(B_695, k1_zfmisc_1(C_694)) | ~r2_hidden(A_693, B_695))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.01/2.67  tff(c_8769, plain, (![A_698]: (m1_subset_1(A_698, '#skF_6') | ~r2_hidden(A_698, '#skF_6'))), inference(resolution, [status(thm)], [c_8300, c_8748])).
% 8.01/2.67  tff(c_8778, plain, (m1_subset_1('#skF_2'('#skF_6'), '#skF_6') | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_7413, c_8769])).
% 8.01/2.67  tff(c_8780, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_8778])).
% 8.01/2.67  tff(c_8799, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8780, c_84])).
% 8.01/2.67  tff(c_8422, plain, (![C_663, B_664, A_665]: (v5_relat_1(C_663, B_664) | ~m1_subset_1(C_663, k1_zfmisc_1(k2_zfmisc_1(A_665, B_664))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.01/2.67  tff(c_8435, plain, (![B_664]: (v5_relat_1('#skF_4', B_664))), inference(resolution, [status(thm)], [c_7402, c_8422])).
% 8.01/2.67  tff(c_8569, plain, (![B_675, A_676]: (r1_tarski(k2_relat_1(B_675), A_676) | ~v5_relat_1(B_675, A_676) | ~v1_relat_1(B_675))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.01/2.67  tff(c_7440, plain, (![A_12]: (~r1_tarski(A_12, '#skF_4') | v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_7400, c_7436])).
% 8.01/2.67  tff(c_8743, plain, (![B_692]: (v1_xboole_0(k2_relat_1(B_692)) | ~v5_relat_1(B_692, '#skF_4') | ~v1_relat_1(B_692))), inference(resolution, [status(thm)], [c_8569, c_7440])).
% 8.01/2.67  tff(c_8963, plain, (![B_714]: (k2_relat_1(B_714)='#skF_4' | ~v5_relat_1(B_714, '#skF_4') | ~v1_relat_1(B_714))), inference(resolution, [status(thm)], [c_8743, c_7418])).
% 8.01/2.67  tff(c_8974, plain, (k2_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8435, c_8963])).
% 8.01/2.67  tff(c_8981, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7474, c_8974])).
% 8.01/2.67  tff(c_8437, plain, (![C_667, A_668, B_669]: (v4_relat_1(C_667, A_668) | ~m1_subset_1(C_667, k1_zfmisc_1(k2_zfmisc_1(A_668, B_669))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.01/2.67  tff(c_8451, plain, (![A_670]: (v4_relat_1('#skF_4', A_670))), inference(resolution, [status(thm)], [c_7402, c_8437])).
% 8.01/2.68  tff(c_8285, plain, (![B_640, A_641]: (r1_tarski(k1_relat_1(B_640), A_641) | ~v4_relat_1(B_640, A_641) | ~v1_relat_1(B_640))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.01/2.68  tff(c_7483, plain, (![A_15]: (A_15='#skF_4' | ~r1_tarski(A_15, '#skF_4'))), inference(resolution, [status(thm)], [c_7433, c_7475])).
% 8.01/2.68  tff(c_8296, plain, (![B_640]: (k1_relat_1(B_640)='#skF_4' | ~v4_relat_1(B_640, '#skF_4') | ~v1_relat_1(B_640))), inference(resolution, [status(thm)], [c_8285, c_7483])).
% 8.01/2.68  tff(c_8455, plain, (k1_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8451, c_8296])).
% 8.01/2.68  tff(c_8458, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7474, c_8455])).
% 8.01/2.68  tff(c_9131, plain, (![B_725, A_726]: (v1_funct_2(B_725, k1_relat_1(B_725), A_726) | ~r1_tarski(k2_relat_1(B_725), A_726) | ~v1_funct_1(B_725) | ~v1_relat_1(B_725))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.01/2.68  tff(c_9137, plain, (![A_726]: (v1_funct_2('#skF_4', '#skF_4', A_726) | ~r1_tarski(k2_relat_1('#skF_4'), A_726) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8458, c_9131])).
% 8.01/2.68  tff(c_9141, plain, (![A_726]: (v1_funct_2('#skF_4', '#skF_4', A_726))), inference(demodulation, [status(thm), theory('equality')], [c_7474, c_8799, c_7433, c_8981, c_9137])).
% 8.01/2.68  tff(c_7441, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7390, c_7390, c_86])).
% 8.01/2.68  tff(c_7442, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_7441])).
% 8.01/2.68  tff(c_8797, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8780, c_7442])).
% 8.01/2.68  tff(c_9145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9141, c_8797])).
% 8.01/2.68  tff(c_9147, plain, ('#skF_6'!='#skF_4'), inference(splitRight, [status(thm)], [c_8778])).
% 8.01/2.68  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.01/2.68  tff(c_8779, plain, (m1_subset_1('#skF_1'('#skF_6'), '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_8769])).
% 8.01/2.68  tff(c_9148, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_8779])).
% 8.01/2.68  tff(c_9151, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_9148, c_7418])).
% 8.01/2.68  tff(c_9155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9147, c_9151])).
% 8.01/2.68  tff(c_9157, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_8779])).
% 8.01/2.68  tff(c_9207, plain, (![C_728, B_729, A_730]: (v1_xboole_0(C_728) | ~m1_subset_1(C_728, k1_zfmisc_1(k2_zfmisc_1(B_729, A_730))) | ~v1_xboole_0(A_730))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.01/2.68  tff(c_9210, plain, (![C_728]: (v1_xboole_0(C_728) | ~m1_subset_1(C_728, k1_zfmisc_1('#skF_6')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8283, c_9207])).
% 8.01/2.68  tff(c_9287, plain, (![C_733]: (v1_xboole_0(C_733) | ~m1_subset_1(C_733, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_7452, c_9210])).
% 8.01/2.68  tff(c_9290, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_8300, c_9287])).
% 8.01/2.68  tff(c_9302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9157, c_9290])).
% 8.01/2.68  tff(c_9303, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_7441])).
% 8.01/2.68  tff(c_9325, plain, (~r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_9303])).
% 8.01/2.68  tff(c_10170, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10153, c_9325])).
% 8.01/2.68  tff(c_10185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7433, c_10170])).
% 8.01/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.68  
% 8.01/2.68  Inference rules
% 8.01/2.68  ----------------------
% 8.01/2.68  #Ref     : 0
% 8.01/2.68  #Sup     : 2030
% 8.01/2.68  #Fact    : 0
% 8.01/2.68  #Define  : 0
% 8.01/2.68  #Split   : 49
% 8.01/2.68  #Chain   : 0
% 8.01/2.68  #Close   : 0
% 8.01/2.68  
% 8.01/2.68  Ordering : KBO
% 8.01/2.68  
% 8.01/2.68  Simplification rules
% 8.01/2.68  ----------------------
% 8.01/2.68  #Subsume      : 414
% 8.01/2.68  #Demod        : 1589
% 8.01/2.68  #Tautology    : 703
% 8.01/2.68  #SimpNegUnit  : 23
% 8.01/2.68  #BackRed      : 247
% 8.01/2.68  
% 8.01/2.68  #Partial instantiations: 0
% 8.01/2.68  #Strategies tried      : 1
% 8.01/2.68  
% 8.01/2.68  Timing (in seconds)
% 8.01/2.68  ----------------------
% 8.01/2.68  Preprocessing        : 0.36
% 8.01/2.68  Parsing              : 0.20
% 8.01/2.68  CNF conversion       : 0.02
% 8.01/2.68  Main loop            : 1.50
% 8.01/2.68  Inferencing          : 0.50
% 8.01/2.68  Reduction            : 0.51
% 8.01/2.68  Demodulation         : 0.34
% 8.01/2.68  BG Simplification    : 0.05
% 8.01/2.68  Subsumption          : 0.31
% 8.01/2.68  Abstraction          : 0.06
% 8.01/2.68  MUC search           : 0.00
% 8.01/2.68  Cooper               : 0.00
% 8.01/2.68  Total                : 1.91
% 8.01/2.68  Index Insertion      : 0.00
% 8.01/2.68  Index Deletion       : 0.00
% 8.01/2.68  Index Matching       : 0.00
% 8.01/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
